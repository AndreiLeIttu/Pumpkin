use std::{fmt::Debug, rc::Rc};

use pumpkin_core::{propagation::LocalId, variables::IntegerVariable};


/// Defines the input of the Disjunctive constraint.
///
/// Each task has a variable starting time and a constant processing time.
#[derive(Debug, Clone)]
pub struct ArgDisjunctiveTask<Var> {
    pub start_time: Var,
    pub processing_time: i32,
}

#[derive(Clone, Debug)]
pub(super) struct DisjunctiveTask<Var> {
    pub(crate) start_time: Var,
    pub(crate) processing_time: i32,
    pub(crate) id: LocalId,
}

impl<Var: IntegerVariable + 'static> DisjunctiveTask<Var> {
    pub(crate) fn get_ect(task: &DisjunctiveTask<Var>, start_time_lb: i32) -> i32 {
        start_time_lb + task.processing_time
    }

    pub(crate) fn get_lct(task: &DisjunctiveTask<Var>, start_time_ub: i32) -> i32 {
        start_time_ub + task.processing_time
    }

    pub(crate) fn get_id(task: &Rc<DisjunctiveTask<Var>>) -> usize {
        task.id.unpack() as usize
    }
}
