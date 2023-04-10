import SmallArray.Basic

namespace SmallArray
  @[simp] theorem push_pop {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop (push_size sa val)
    sa' = sa ∧ val' = val:= by
    simp
    cases sa
    <;> simp [push, pop]
    <;> try rfl
    . apply And.intro
      . simp [Array.pop, Array.get, GetElem.getElem]
      . simp [GetElem.getElem]
        rfl
    case Array arr =>
      rw [apply_ite (fun x => Prod.snd x)]
      rw [apply_ite (fun x => Prod.fst x)]
      simp
      have h: 1 < arr.val.size:= arr.property
      apply Nat.not_le_of_lt h

  @[simp] theorem push_pop? {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop?
    sa' = sa ∧ val' = some val:= by
    simp [pop?]
end SmallArray
