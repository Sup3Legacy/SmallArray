import SmallArray.Basic

namespace SmallArray
  @[simp] theorem push_pop {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop (push_size sa val)
    sa' = sa ∧ val' = val:= by
    cases sa
    <;> simp [push, pop, Array.size_pop, ge_iff_le, and_self,
      Array.get_eq_getElem]
    <;> try rfl
    . apply And.intro
      . simp only [Array.get, GetElem.getElem, List.get]
      . simp only [GetElem.getElem, Fin.mk_one, Array.get_eq_getElem, Fin.val_one]
        rfl
    case Array arr =>
      rw [apply_ite (fun x => Prod.snd x)]
      rw [apply_ite (fun x => Prod.fst x)]
      simp only [ite_eq_left_iff, not_lt, ite_self, and_true]
      have h: 1 < arr.val.size:= arr.property
      apply Nat.not_le_of_lt h

  @[simp] theorem push_pop? {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop?
    sa' = sa ∧ val' = some val:= by
    simp only [pop?, push_size, push_pop, dite_eq_ite, ite_true, and_self]
end SmallArray
