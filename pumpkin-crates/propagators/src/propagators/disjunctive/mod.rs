//! Contains the propagator for the [Disjunctive](https://sofdem.github.io/gccat/gccat/Cdisjunctive.html) constraint.
//!
//! Currently, it contains only an edge-finding propagator.
use pumpkin_core::declare_inference_label;

pub(crate) mod disjunctive_propagator;
pub(crate) mod disjunctive_task;
pub(crate) mod detectable_precedences;
mod theta_lambda_tree;
mod theta_tree;
pub use disjunctive_propagator::DisjunctiveConstructor;
pub use disjunctive_propagator::DisjunctivePropagator;
pub use disjunctive_task::ArgDisjunctiveTask;
pub use detectable_precedences::DetectablePrecedencesPropagator;
pub(crate) mod checker;
pub use checker::*;
pub(crate) mod utils;
pub(crate) use utils::*;

declare_inference_label!(DisjunctiveEdgeFinding);
declare_inference_label!(DisjunctineDetectablePrecedences);
