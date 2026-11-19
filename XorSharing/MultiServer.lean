import XorSharing.TwoServer

namespace XorSharing

def shareThree {w : Nat} (secret mask1 mask2 : BitString w) :
    BitString w × (BitString w × BitString w) :=
  (mask1, (mask2, xorBits (xorBits mask1 mask2) secret))

def reconstructThree {w : Nat}
    (shares : BitString w × (BitString w × BitString w)) :
    BitString w :=
  xorBits (xorBits shares.1 shares.2.1) shares.2.2

theorem reconstruct_share_three {w : Nat}
    (secret mask1 mask2 : BitString w) :
    reconstructThree (shareThree secret mask1 mask2) = secret := by
  change reconstruct (share secret (xorBits mask1 mask2)) = secret
  exact reconstruct_share secret (xorBits mask1 mask2)

def zeroBits {w : Nat} : BitString w :=
  fun _ => false

def xorAll {w : Nat} (strings : List (BitString w)) : BitString w :=
  strings.foldl xorBits zeroBits

def shareMany {w : Nat} (secret : BitString w)
    (masks : List (BitString w)) : List (BitString w) :=
  masks ++ [xorBits (xorAll masks) secret]

def reconstructMany {w : Nat}
    (shares : List (BitString w)) : BitString w :=
  xorAll shares

theorem reconstruct_share_many {w : Nat} (secret : BitString w)
    (masks : List (BitString w)) :
    reconstructMany (shareMany secret masks) = secret := by
  unfold reconstructMany shareMany xorAll
  rw [List.foldl_append]
  change reconstruct (share secret (xorAll masks)) = secret
  exact reconstruct_share secret (xorAll masks)



def shareAt {w m : Nat} (secret : BitString w)
    (masks : Fin m → BitString w) (server : Option (Fin m)) :
    BitString w :=
  match server with
  | some i => masks i
  | none   => xorBits (xorAll (List.ofFn masks)) secret

def groupView {w m : Nat} (secret : BitString w)
    (masks : Fin m → BitString w) (visible : Set (Option (Fin m))) :
    {server // server ∈ visible} → BitString w :=
  fun server => shareAt secret masks server.val

theorem group_view_without_final {w m : Nat} (s t : BitString w)
    (masks : Fin m → BitString w) (visible : Set (Option (Fin m)))
    (hfinal : none ∉ visible) :
    groupView s masks visible = groupView t masks visible := by
  funext member
  obtain ⟨server, hmem⟩ := member
  cases server with
  | none   => exact (hfinal hmem).elim
  | some i => rfl


def adjustMask {w m : Nat} (masks : Fin m → BitString w)
    (hidden : Fin m) (delta : BitString w) : Fin m → BitString w :=
  fun i => if i = hidden then xorBits (masks i) delta else masks i

theorem adjustMask_other {w m : Nat} (masks : Fin m → BitString w)
    (hidden i : Fin m) (delta : BitString w) (hi : i ≠ hidden) :
    adjustMask masks hidden delta i = masks i := by
  simp [adjustMask, hi]

theorem adjustMask_twice {w m : Nat} (masks : Fin m → BitString w)
    (hidden : Fin m) (delta : BitString w) :
    adjustMask (adjustMask masks hidden delta) hidden delta = masks := by
  funext i
  by_cases hi : i = hidden
  · simp [adjustMask, hi, xorBits_cancel_right]
  · simp [adjustMask, hi]

theorem xorBits_assoc {w : Nat} (a b c : BitString w) :
    xorBits (xorBits a b) c = xorBits a (xorBits b c) := by
  funext i
  change Bool.xor (Bool.xor (a i) (b i)) (c i) =
    Bool.xor (a i) (Bool.xor (b i) (c i))
  cases (a i) <;> cases (b i) <;> cases (c i) <;> rfl

theorem xorAll_cons {w : Nat}
    (head : BitString w) (tail : List (BitString w)) :
    xorAll (head :: tail) = xorBits head (xorAll tail) := by
  let : Std.Associative (@xorBits w) := ⟨xorBits_assoc⟩
  have hzero : xorBits zeroBits head = xorBits head zeroBits := by
    funext i
    change Bool.xor false (head i) = Bool.xor (head i) false
    cases (head i) <;> rfl
  change tail.foldl xorBits (xorBits zeroBits head) =
    xorBits head (tail.foldl xorBits zeroBits)
  rw [hzero]
  exact List.foldl_assoc

theorem xorAll_adjustMask {w m : Nat} (masks : Fin m → BitString w)
    (hidden : Fin m) (delta : BitString w) :
    xorAll (List.ofFn (adjustMask masks hidden delta)) =
      xorBits (xorAll (List.ofFn masks)) delta := by
  induction m with
  | zero =>
      exact Fin.elim0 hidden
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) hidden
      · have htail :
            (fun i : Fin m => adjustMask masks 0 delta i.succ) =
              (fun i : Fin m => masks i.succ) := by
          funext i
          exact adjustMask_other masks 0 i.succ delta (Fin.succ_ne_zero i)
        simp only [List.ofFn_succ, xorAll_cons]
        rw [htail]
        simp only [adjustMask]
        generalize xorAll (List.ofFn (fun i : Fin m => masks i.succ)) = tail
        funext i
        change Bool.xor (Bool.xor (masks 0 i) (delta i)) (tail i) =
          Bool.xor (Bool.xor (masks 0 i) (tail i)) (delta i)
        cases (masks 0 i) <;> cases (delta i) <;> cases (tail i) <;> rfl
      · have hhead : adjustMask masks j.succ delta 0 = masks 0 :=
          adjustMask_other masks j.succ 0 delta (Ne.symm (Fin.succ_ne_zero j))
        have htail :
            (fun i : Fin m => adjustMask masks j.succ delta i.succ) =
              adjustMask (fun i : Fin m => masks i.succ) j delta := by
          funext i
          simp only [adjustMask, Fin.succ_inj]
        simp only [List.ofFn_succ, xorAll_cons, hhead, htail]
        rw [ih (fun i => masks i.succ) j]
        exact (xorBits_assoc _ _ _).symm

theorem final_share_adjustMask {w m : Nat} (s t : BitString w)
    (masks : Fin m → BitString w) (hidden : Fin m) :
    shareAt t (adjustMask masks hidden (xorBits s t)) none =
      shareAt s masks none := by
  change
    xorBits (xorAll (List.ofFn (adjustMask masks hidden (xorBits s t)))) t =
      xorBits (xorAll (List.ofFn masks)) s
  rw [xorAll_adjustMask, xorBits_assoc, xorBits_cancel_right]

theorem group_view_adjustMask {w m : Nat} (s t : BitString w)
    (masks : Fin m → BitString w) (visible : Set (Option (Fin m)))
    (hidden : Fin m) (hhidden : some hidden ∉ visible) :
    groupView t (adjustMask masks hidden (xorBits s t)) visible =
      groupView s masks visible := by
  funext member
  obtain ⟨server, hmem⟩ := member
  cases server with
  | none =>
      exact final_share_adjustMask s t masks hidden
  | some i =>
      have hi : i ≠ hidden := by
        intro heq
        subst i
        exact hhidden hmem
      exact adjustMask_other masks hidden i (xorBits s t) hi

-- A mask tuple together with proof that it produces the observed view.
def MasksForView {w m : Nat} (secret : BitString w)
    (visible : Set (Option (Fin m)))
    (observed : {server // server ∈ visible} → BitString w) : Type :=
  {masks : Fin m → BitString w // groupView secret masks visible = observed}

theorem multi_server_privacy {w m : Nat} (s t : BitString w)
    (visible : Set (Option (Fin m)))
    (observed : {server // server ∈ visible} → BitString w)
    (hmissing : ∃ server : Option (Fin m), server ∉ visible) :
    Nat.card (MasksForView s visible observed) =
      Nat.card (MasksForView t visible observed) := by
  obtain ⟨server, hserver⟩ := hmissing
  apply Nat.card_congr
  cases server with
  | none =>
      refine Equiv.subtypeEquiv (Equiv.refl (Fin m → BitString w)) ?_
      intro masks
      change (groupView s masks visible = observed) ↔
        (groupView t masks visible = observed)
      rw [group_view_without_final s t masks visible hserver]
  | some hidden =>
      let delta := xorBits s t
      let adjust : (Fin m → BitString w) ≃ (Fin m → BitString w) :=
        { toFun := fun masks => adjustMask masks hidden delta
          invFun := fun masks => adjustMask masks hidden delta
          left_inv := fun masks => adjustMask_twice masks hidden delta
          right_inv := fun masks => adjustMask_twice masks hidden delta }
      refine Equiv.subtypeEquiv adjust ?_
      intro masks
      change (groupView s masks visible = observed) ↔
        (groupView t (adjustMask masks hidden (xorBits s t)) visible = observed)
      rw [group_view_adjustMask s t masks visible hidden hserver]

noncomputable def viewProbability {w m : Nat} (secret : BitString w)
    (visible : Set (Option (Fin m)))
    (observed : {server // server ∈ visible} → BitString w) : ℚ :=
  (Nat.card (MasksForView secret visible observed) : ℚ) /
    (Nat.card (Fin m → BitString w) : ℚ)

theorem multi_server_perfect_privacy {w m : Nat} (s t : BitString w)
    (visible : Set (Option (Fin m)))
    (observed : {server // server ∈ visible} → BitString w)
    (hmissing : ∃ server : Option (Fin m), server ∉ visible) :
    viewProbability s visible observed =
      viewProbability t visible observed := by
  unfold viewProbability
  rw [multi_server_privacy s t visible observed hmissing]

end XorSharing
