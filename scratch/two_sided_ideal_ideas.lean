import Mathlib.Algebra.Quaternion

variable (D : Type) [Add D] [Mul D] in
#check IsSimpleOrder (RingCon D)

variable (R : Type) [Ring R]

namespace RingCon
variable (e : RingCon R)

def toTwoSidedIdeal : Submodule R R where
  carrier := {x | e x 0}
  add_mem' {s} {t} hₛ hₜ := (add_zero (0 : R)) ▸ e.add hₛ hₜ
  zero_mem' := e.refl 0
  smul_mem' c x (hx0 : e x 0) := by
    dsimp
    have := e.mul (e.refl c) (hx0)
    convert this
    simp

variable {R}

abbrev I := e.toTwoSidedIdeal

def e' (a b : R) : Prop := a - b ∈ e.I

theorem e'_eq_e : ∀ x y : R, e.e' x y ↔ e x y := by
  intros x y
  unfold e'
  unfold I
  unfold toTwoSidedIdeal
  simp

  sorry

end RingCon
