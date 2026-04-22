use std::cmp::max;
use std::cmp::min;
use std::collections::HashMap;
use std::rc::Rc;

use crate::disjunctive::disjunctive_task::DisjunctiveTask;
use super::UnionFind;
use pumpkin_core::propagation::Domains;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::ReadDomains;
use pumpkin_core::variables::IntegerVariable;

pub(crate) struct Timeline {
    pub(crate) t: Vec<i32>,
    pub(crate) c: Vec<i32>,
    pub(crate) m: Vec<i32>,
    pub(crate) e: i32,
    pub(crate) s: UnionFind,
    pub(crate) u: Vec<Vec<LocalId>>,
    pub(crate) lower: i32,
}

impl Timeline {
    pub(crate) fn new<Var: IntegerVariable + 'static>(
        tasks: Rc<[DisjunctiveTask<Var>]>,
        context: &Domains,
    ) -> Self {
        let mut tasks_est = tasks.iter().cloned().collect::<Vec<DisjunctiveTask<Var>>>();
        tasks_est.sort_by_key(|a| context.lower_bound(&a.start_time));

        let mut t = vec![];
        let mut c = vec![];
        let mut m: Vec<i32> = vec![0; tasks_est.len()];

        for task in tasks_est.iter() {
            let est = context.lower_bound(&task.start_time);
            if t.len() == 0 || t[t.len() - 1] != est {
                t.push(est);
            }
            m[DisjunctiveTask::get_id(&Rc::new(task.clone()))] = (t.len() - 1) as i32;
        }
        let highest_lct = tasks
            .iter()
            .map(|task| DisjunctiveTask::get_lct(task, context.upper_bound(&task.start_time)))
            .max()
            .unwrap();
        t.push(highest_lct + tasks.iter().map(|task| task.processing_time).sum::<i32>());
        for k in 0..t.len() - 1 {
            c.push(t[k + 1] - t[k]);
        }
        let n = t.len();
        let lower = tasks.iter().map(|task| context.lower_bound(&task.start_time)).min().unwrap();
        Timeline {
            t: t,
            c: c,
            m: m,
            e: -1,
            s: UnionFind::new(n as i32),
            u: vec![vec![]; n],
            lower: lower,
        }
    }

    pub(crate) fn schedule_task<Var: IntegerVariable + 'static>(
        &mut self,
        task: &Rc<DisjunctiveTask<Var>>,
    ) -> () {
        let mut rho = task.processing_time;
        let mut k = self.s.find(self.m[DisjunctiveTask::get_id(task)]) as usize;

        while rho > 0 {
            let delta = min(self.c[k], rho);
            rho -= delta;
            self.c[k] -= delta;
            if self.c[k] == 0 {
                let a = k;
                let _ = self.s.union(k as i32, (k + 1) as i32);
                k = self.s.find(k as i32) as usize;
                if a != k {
                    let b = self.u[a].clone();
                    self.u[k].extend(b.iter());
                } else {
                    panic!("This should not happen, the union-find structure is broken");
                }
            }
            if rho == 0 {
                self.u[k].push(task.id);
            }
        }
        self.e = max(self.e, k as i32);
    }

    pub(crate) fn earliest_completion_time(&self) -> i32 {
        if self.e == -1 {
            return self.lower;
        }
        self.t[(self.e + 1) as usize] - self.c[self.e as usize]
    }

    pub(crate) fn get_omega(&self) -> Vec<LocalId> {
        if self.e == -1 {
            return vec![];
        }
        
        let omega = self.u[self.e as usize].clone();
        omega
    }
    
    fn print_uf(&mut self) {
        let mut uf_map: HashMap<i32, Vec<i32>> = HashMap::new();
        for i in 0..self.s.size() {
            let root = self.s.find(i);
            uf_map.entry(root).or_insert_with(Vec::new).push(i);
        }
        let mut vals = uf_map.values().cloned().collect::<Vec<Vec<i32>>>();
        vals.iter_mut().for_each(|i| {
            i.sort();
        });
        vals.sort();
        println!("{:?}", vals);
    }
}