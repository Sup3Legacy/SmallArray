import SmallArray.Basic

namespace SmallArray
  @[simp] theorem push_pop {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop (push_size sa val)
    sa' = sa ∧ val' = val:= by
    cases sa
    <;> simp [push, pop, Array.size_pop, ge_iff_le, and_self,
      Array.get_eq_getElem]
    case Some _ =>
      simp only [Array.get, GetElem.getElem, List.get]
    case Array arr =>
      simp only [apply_ite, ite_eq_left_iff, not_lt, ite_self, and_true]
      apply Nat.not_le_of_lt arr.property

  @[simp] theorem push_pop? {α : Type u} (sa: SmallArray α) (val: α):
    let (sa', val') := (sa.push val).pop?
    sa' = sa ∧ val' = some val:= by
    simp only [pop?, push_size, push_pop, dite_eq_ite, ite_true, and_self]
end SmallArray
