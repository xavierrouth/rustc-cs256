//! Dataflow analyses are built upon some interpretation of the
//! bitvectors attached to each basic block, represented via a
//! zero-sized structure.

pub mod anticipated;
pub mod available;
mod borrowed_locals;
mod initialized;
mod liveness;
pub mod postponable;
pub mod pre_analysis;
mod storage_liveness;
pub mod used;

pub use self::anticipated::{AnticipatedExpressions, AnticipatedExpressionsResults};
pub use self::available::{AvailableExpressions, AvailableExpressionsResults};
pub use self::borrowed_locals::borrowed_locals;
pub use self::borrowed_locals::MaybeBorrowedLocals;
pub use self::initialized::{
    DefinitelyInitializedPlaces, EverInitializedPlaces, MaybeInitializedPlaces,
    MaybeUninitializedPlaces,
};
pub use self::liveness::MaybeLiveLocals;
pub use self::liveness::MaybeTransitiveLiveLocals;
pub use self::liveness::TransferFunction as LivenessTransferFunction;
pub use self::postponable::PostponableExpressions;
pub use self::pre_analysis::*;
pub use self::storage_liveness::{MaybeRequiresStorage, MaybeStorageDead, MaybeStorageLive};
pub use self::used::UsedExpressions;
