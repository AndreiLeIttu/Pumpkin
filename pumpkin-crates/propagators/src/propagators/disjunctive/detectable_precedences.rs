use std::collections::HashMap;
use std::rc::Rc;

use pumpkin_core::conjunction;
use pumpkin_core::predicate;
use pumpkin_core::predicates::PropositionalConjunction;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::DomainEvents;
use pumpkin_core::propagation::Domains;
use pumpkin_core::propagation::InferenceCheckers;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
use pumpkin_core::propagation::ReadDomains;
use pumpkin_core::results::PropagationStatusCP;
use pumpkin_core::state::Conflict;
use pumpkin_core::state::PropagatorConflict;
use pumpkin_core::variables::IntegerVariable;
use pumpkin_core::variables::TransformableVariable;

use super::disjunctive_task::ArgDisjunctiveTask;
use super::disjunctive_task::DisjunctiveTask;
use crate::disjunctive::DisjunctiveDetectablePrecedences;
use crate::disjunctive::Timeline;
use crate::disjunctive::checker::DisjunctiveEdgeFindingChecker;

/// [`Propagator`] responsible for using one variant of disjunctive reasoning to propagate the [Disjunctive](https://sofdem.github.io/gccat/gccat/Cdisjunctive.html) constraint.
///
/// Currently, this propagator only implements detectable precedences as specified in \[1\] with explanations
/// based on \[2\]. The reasoning of this approach is based on finding a task i and a subset of
/// tasks for which it holds that if we were to schedule i at its earliest start time then it would
/// overflow the resource capacity and thus i should be scheduled after all activities from this
/// set.
///
/// It follows the [MiniZinc specifications](https://docs.minizinc.dev/en/stable/lib-globals-scheduling.html#mzn-ref-globals-scheduling-disjunctive-strict) which means that tasks with duration 0 can only be scheduled when no other tasks are running.
///
///
/// # Bibliography
/// - \[1\] H. Fahimi and C. G. Quimper, ‘Linear-time filtering algorithms for the disjunctive constraint’, in Proceedings of the AAAI Conference on Artificial Intelligence, vol. 28, no. 1, Jun. 2014.
/// - \[2\] M. B. van Vliet, ‘Explaining detectable precedences for the disjunctive constraint’.
#[derive(Debug, Clone)]
pub struct DetectablePrecedencesPropagator<Var: IntegerVariable> {
    /// The tasks which serve as the input to the disjunctive constraint
    tasks: Box<[DisjunctiveTask<Var>]>,
    /// An additional list of tasks used as a view
    reversed_tasks: Box<[DisjunctiveTask<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>]>,
    i_ect: Vec<DisjunctiveTask<Var>>,
    i_lst: Vec<DisjunctiveTask<Var>>,
    i_ect_rev: Vec<DisjunctiveTask<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>>,
    i_lst_rev: Vec<DisjunctiveTask<<<Var as IntegerVariable>::AffineView as IntegerVariable>::AffineView>>,
    root_bounds: Vec<(i32, i32)>,
    root_bounds_rev: Vec<(i32, i32)>,

    inference_code: InferenceCode,
}

#[derive(Debug)]
pub struct DetectablePrecedencesConstructor<Var> {
    constraint_tag: ConstraintTag,
    tasks: Vec<ArgDisjunctiveTask<Var>>,
}

impl<Var> DetectablePrecedencesConstructor<Var> {
    pub fn new(
        tasks: impl IntoIterator<Item = ArgDisjunctiveTask<Var>>,
        constraint_tag: ConstraintTag,
    ) -> Self {
        Self {
            constraint_tag,
            tasks: tasks.into_iter().collect(),
        }
    }
}

impl<Var: IntegerVariable + 'static> PropagatorConstructor for DetectablePrecedencesConstructor<Var> {
    type PropagatorImpl = DetectablePrecedencesPropagator<Var>;

    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        let tasks = self
            .tasks
            .iter()
            .enumerate()
            .map(|(index, task)| DisjunctiveTask {
                start_time: task.start_time.clone(),
                processing_time: task.processing_time,
                id: LocalId::from(index as u32),
            })
            .collect::<Vec<_>>();

        let reversed_tasks = tasks  
            .iter()
            .map(|task| DisjunctiveTask {
                start_time: task.start_time.clone().offset(task.processing_time).scaled(-1),
                processing_time: task.processing_time,
                id: task.id,
            })
            .collect::<Vec<_>>();

        let mut root_bounds = vec![];
        let mut root_bounds_rev = vec![];

        for i in 0..tasks.len() {
            let est_i = context.lower_bound(&tasks[i].start_time);
            let lst_i = context.upper_bound(&tasks[i].start_time);

            let rev_est_i = context.lower_bound(&reversed_tasks[i].start_time);
            let rev_lst_i = context.upper_bound(&reversed_tasks[i].start_time);

            root_bounds.push((est_i, lst_i));
            root_bounds_rev.push((rev_est_i, rev_lst_i));
        }

        let inference_code = InferenceCode::new(self.constraint_tag, DisjunctiveDetectablePrecedences);

        tasks.iter().for_each(|task| {
            context.register(task.start_time.clone(), DomainEvents::BOUNDS, task.id);
        });

        DetectablePrecedencesPropagator {
            tasks: tasks.clone().into_boxed_slice(),
            reversed_tasks: reversed_tasks.clone().into_boxed_slice(),
            i_ect: tasks.clone(),
            i_lst: tasks.clone(),
            i_ect_rev: reversed_tasks.clone(),
            i_lst_rev: reversed_tasks.clone(),
            root_bounds: root_bounds,
            root_bounds_rev: root_bounds_rev,
            inference_code,
        }
    }

    fn add_inference_checkers(&self, mut checkers: InferenceCheckers<'_>) {
        checkers.add_inference_checker(
            InferenceCode::new(self.constraint_tag, DisjunctiveDetectablePrecedences),
            Box::new(DisjunctiveEdgeFindingChecker {
                tasks: self
                    .tasks
                    .iter()
                    .map(|task| ArgDisjunctiveTask {
                        start_time: task.start_time.clone(),
                        processing_time: task.processing_time,
                    })
                    .collect(),
            }),
        );
    }
}

impl<Var: IntegerVariable + 'static> Propagator for DetectablePrecedencesPropagator<Var> {
    fn name(&self) -> &str {
        "DisjunctiveDetectablePrecedences"
    }

    fn propagate(&mut self, mut context: PropagationContext) -> PropagationStatusCP {
        self.i_ect.sort_by_key(|a| DisjunctiveTask::get_ect(&a, context.lower_bound(&a.start_time)));
        self.i_lst.sort_by_key(|a| context.upper_bound(&a.start_time));
        detectable_precedences(&self.tasks, &mut context, &self.i_ect, &self.i_lst, &self.root_bounds, &self.inference_code)?;

        self.i_ect_rev.sort_by_key(|a| DisjunctiveTask::get_ect(&a, context.lower_bound(&a.start_time)));
        self.i_lst_rev.sort_by_key(|a| context.upper_bound(&a.start_time));
        detectable_precedences(&self.reversed_tasks, &mut context, &self.i_ect_rev, &self.i_lst_rev, &self.root_bounds_rev, &self.inference_code)
    }

    fn propagate_from_scratch(&self, mut context: PropagationContext) -> PropagationStatusCP {
        let mut i_ect = self.i_ect.clone();
        let mut i_lst = self.i_lst.clone();
        let mut i_ect_rev = self.i_ect_rev.clone();
        let mut i_lst_rev = self.i_lst_rev.clone();
        i_ect.sort_by_key(|a| DisjunctiveTask::get_ect(&a, context.lower_bound(&a.start_time)));
        i_lst.sort_by_key(|a| context.upper_bound(&a.start_time));
        detectable_precedences(&self.tasks, &mut context, &i_ect, &i_lst, &self.root_bounds, &self.inference_code)?;

        i_ect_rev.sort_by_key(|a| DisjunctiveTask::get_ect(&a, context.lower_bound(&a.start_time)));
        i_lst_rev.sort_by_key(|a| context.upper_bound(&a.start_time));
        detectable_precedences(&self.reversed_tasks, &mut context, &i_ect_rev, &i_lst_rev, &self.root_bounds_rev, &self.inference_code)
    }
}


fn detectable_precedences<Var:IntegerVariable + 'static>(
    tasks: &[DisjunctiveTask<Var>],
    context: &mut PropagationContext, 
    i_ect: &Vec<DisjunctiveTask<Var>>, 
    i_lst: &Vec<DisjunctiveTask<Var>>,
    root_bounds: &Vec<(i32, i32)>,
    inference_code: &InferenceCode,
) -> PropagationStatusCP {
    let mut timeline = Timeline::new(tasks.into(), &context.domains());

    let mut j = 0;
    let mut k = i_lst[0].clone();
    let mut ect_k = DisjunctiveTask::get_ect(&k, context.lower_bound(&k.start_time));
    let mut lst_k = context.upper_bound(&k.start_time);
    let mut blocking_task: Option<DisjunctiveTask<Var>> = None;
    let mut postponed_tasks: Vec<DisjunctiveTask<Var>> = vec![];
    let mut propagations: HashMap<LocalId, (i32, PropositionalConjunction)> = HashMap::default();
    for i in i_ect.iter() {
        let ect_i = DisjunctiveTask::get_ect(i, context.lower_bound(&i.start_time));
        while j < i_lst.len() - 1 && lst_k < ect_i {
            if lst_k >= ect_k {
                timeline.schedule_task(&Rc::new(k.clone()));
            } else {
                if matches!(blocking_task, Some(_)) {
                    let block_task = blocking_task.clone().unwrap();
                    let r = get_conflict_explanation(&block_task, &k, context.domains());
                    return Err(Conflict::Propagator(PropagatorConflict {
                        conjunction: r,
                        inference_code: inference_code.clone(),
                    }));
                }
                blocking_task = Some(k.clone());
            }
            j += 1;
            k = i_lst[j].clone();
            ect_k = DisjunctiveTask::get_ect(&k, context.lower_bound(&k.start_time));
            lst_k = context.upper_bound(&k.start_time);
        }
        if matches!(blocking_task, None) {
            let ect_timeline = timeline.earliest_completion_time();
            if !propagations.contains_key(&i.id)
                || ect_timeline > propagations.get(&i.id).unwrap().0
            {
                let reason = get_propagation_explanation(i,tasks,  &timeline, &context.domains(), root_bounds);
                let _ = propagations.insert(i.id, (ect_timeline, reason.clone()));
            }
        } else {
            let Some(ref x) = blocking_task else {
                panic!("This should not happen");
            };
            if i.id == x.id {
                let mut ect_timeline = timeline.earliest_completion_time();
                if !propagations.contains_key(&i.id)
                    || ect_timeline > propagations.get(&i.id).unwrap().0
                {
                    let reason = get_propagation_explanation(i, tasks, &timeline, &context.domains(), root_bounds);
                    let _ = propagations.insert(i.id, (ect_timeline, reason.clone()));
                }
                timeline.schedule_task(&Rc::new(i.clone()));
                blocking_task = None;
                ect_timeline = timeline.earliest_completion_time();
                for z in postponed_tasks.iter() {
                    if !propagations.contains_key(&z.id)
                        || ect_timeline > propagations.get(&z.id).unwrap().0
                    {
                        let reason = get_propagation_explanation(z, tasks, &timeline, &context.domains(), root_bounds);
                        let _ = propagations.insert(z.id, (ect_timeline, reason.clone()));
                    }
                }
                postponed_tasks.clear();
            } else {
                postponed_tasks.push(i.clone());
            }
        }
    }
    for i in i_ect.iter().rev() {
        if !propagations.contains_key(&i.id) {
            continue;
        }
        //let task = &tasks[id.unpack() as usize];
        let (ect, reason) = propagations.get(&i.id).unwrap();
        if *ect <= context.lower_bound(&i.start_time) {
            continue;
        }
        let _x = context.post(
            predicate!(i.start_time >=*ect),
            reason.clone(),
            inference_code
        )?;
    }

    Ok(())
}

fn get_propagation_explanation<Var: IntegerVariable + 'static>(
    task: &DisjunctiveTask<Var>,
    tasks: &[DisjunctiveTask<Var>], 
    timeline: &Timeline, 
    domains: &Domains,
    root_bounds: &Vec<(i32, i32)>
) -> PropositionalConjunction {
    let mut reason = PropositionalConjunction::new(vec![]);
    let omega = timeline.get_omega();
    
    if omega.is_empty() {
        reason.push(predicate![task.start_time >= domains.lower_bound(&task.start_time)]);
        return reason;
    }

    let mut est_omega = std::i32::MAX;
    let mut lst_omega = std::i32::MIN;

    for &omega_task_id in omega.iter() {
        let omega_task = tasks[omega_task_id.unpack() as usize].clone();
        est_omega = est_omega.min(domains.lower_bound(&omega_task.start_time));
        lst_omega = lst_omega.max(domains.upper_bound(&omega_task.start_time));
    }

    let est_i = domains.lower_bound(&task.start_time);
    let p_i = task.processing_time;
    let est_i_lift = est_i.min(lst_omega - p_i + 1);
    if root_bounds[task.id.unpack() as usize].0 <= est_i_lift {
        reason.push(predicate![task.start_time >= est_i_lift]);
    }

    reason.extend(omega.iter().flat_map(|t_id| {
        let om_task = tasks[t_id.unpack() as usize].clone();
        let mut om_reason = vec![];
        if root_bounds[t_id.unpack() as usize].0 <= est_omega {
            om_reason.push(predicate![om_task.start_time >= est_omega]);
        }

        if root_bounds[t_id.unpack() as usize].1 >= lst_omega {
            om_reason.push(predicate![om_task.start_time <= lst_omega]);
        }

        om_reason
    }));

    reason
}

fn get_conflict_explanation<Var: IntegerVariable + 'static>(
    a: &DisjunctiveTask<Var>,
    b: &DisjunctiveTask<Var>,
    context: Domains,
) -> PropositionalConjunction {

    return conjunction!(
        [a.start_time >= context.lower_bound(&a.start_time)] &
        [a.start_time <= context.upper_bound(&a.start_time)] &
        [b.start_time >= context.lower_bound(&b.start_time)] &
        [b.start_time <= context.upper_bound(&b.start_time)]
    );
}

#[allow(deprecated, reason = "Will be refactored")]
#[cfg(test)]
mod tests {
    use pumpkin_core::TestSolver;

    use crate::disjunctive::ArgDisjunctiveTask;
    use crate::disjunctive::DisjunctiveConstructor;

    #[test]
    fn propagator_propagates_lower_bound() {
        let mut solver = TestSolver::default();
        let c = solver.new_variable(4, 26);
        let d = solver.new_variable(13, 13);
        let e = solver.new_variable(5, 10);
        let f = solver.new_variable(5, 10);

        let constraint_tag = solver.new_constraint_tag();
        let _ = solver
            .new_propagator(DisjunctiveConstructor::new(
                [
                    ArgDisjunctiveTask {
                        start_time: c,
                        processing_time: 4,
                    },
                    ArgDisjunctiveTask {
                        start_time: d,
                        processing_time: 5,
                    },
                    ArgDisjunctiveTask {
                        start_time: e,
                        processing_time: 3,
                    },
                    ArgDisjunctiveTask {
                        start_time: f,
                        processing_time: 3,
                    },
                ],
                constraint_tag,
            ))
            .expect("No conflict");
        assert_eq!(solver.lower_bound(c), 18);
    }
}
