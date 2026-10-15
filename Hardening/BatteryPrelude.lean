/-
Convention battery PRELUDE (generated, shared by shards A-D).
See Hardening/ConventionBattery.lean header for provenance.
-/
import ConnectionLaplacian

namespace Hardening

open ConnectionLaplacian ConnGraph Matrix BigOperators

set_option maxHeartbeats 4000000

/-- Bridge lemma: lift a `decide`-provable card over a finite type to R. -/
theorem card_filter_univ_cast {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (k : ℕ)
    (h : (Finset.filter p Finset.univ).card = k) :
    ((Finset.filter p Finset.univ).card : ℝ) = k := by rw [h]

end Hardening
