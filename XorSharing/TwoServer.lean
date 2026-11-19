import Mathlib
namespace XorSharing

theorem xor_recover_bit (mask secret : Bool) :
    Bool.xor mask (Bool.xor mask secret) = secret := by
  cases mask <;> cases secret <;> rfl

def BitString (w : Nat) := Fin w → Bool

def xorBits {w : Nat} (a b : BitString w) : BitString w :=
  fun i => Bool.xor (a i) (b i)

def share {w : Nat} (secret mask : BitString w) :
    BitString w × BitString w :=
  (mask, xorBits mask secret)

def reconstruct {w : Nat} (shares : BitString w × BitString w) :
    BitString w :=
  xorBits shares.1 shares.2

theorem reconstruct_share {w : Nat} (secret mask : BitString w) :
    reconstruct (share secret mask) = secret := by
  funext i
  exact xor_recover_bit (mask i) (secret i)


theorem xorBits_cancel_right {w : Nat} (value key : BitString w) :
    xorBits (xorBits value key) key = value := by
  funext i
  change Bool.xor (Bool.xor (value i) (key i)) (key i) = value i
  cases (value i) <;> cases (key i) <;> rfl


theorem first_share_unique_mask {w : Nat} (secret observed : BitString w) :
    ∃! mask : BitString w, (share secret mask).1 = observed := by
  refine ⟨observed, rfl, ?_⟩
  intro mask h
  exact h

theorem second_share_unique_mask {w : Nat} (secret observed : BitString w) :
    ∃! mask : BitString w, (share secret mask).2 = observed := by
  refine ⟨xorBits observed secret, ?_, ?_⟩
  · exact xorBits_cancel_right observed secret
  · intro mask h
    change xorBits mask secret = observed at h
    calc
      mask = xorBits (xorBits mask secret) secret :=
        (xorBits_cancel_right mask secret).symm
      _ = xorBits observed secret :=
        congrArg (fun x => xorBits x secret) h


theorem count_eq_one_of_unique {α : Type} {p : α → Prop}
    (h : ExistsUnique p) : ({x : α | p x} : Set α).ncard = 1 := by
  obtain ⟨witness, hw, unique⟩ := h
  apply Set.ncard_eq_one.mpr
  refine ⟨witness, ?_⟩
  ext x
  change p x ↔ x = witness
  constructor
  · exact unique x
  · intro hx
    rw [hx]
    exact hw

theorem two_server_privacy {w : Nat} (s t observed : BitString w) :
    ({mask : BitString w | (share s mask).1 = observed} : Set _).ncard =
      ({mask : BitString w | (share t mask).1 = observed} : Set _).ncard ∧
    ({mask : BitString w | (share s mask).2 = observed} : Set _).ncard =
      ({mask : BitString w | (share t mask).2 = observed} : Set _).ncard := by
  constructor
  · exact (count_eq_one_of_unique (first_share_unique_mask s observed)).trans
      (count_eq_one_of_unique (first_share_unique_mask t observed)).symm
  · exact (count_eq_one_of_unique (second_share_unique_mask s observed)).trans
      (count_eq_one_of_unique (second_share_unique_mask t observed)).symm
end XorSharing
