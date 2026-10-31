import EA.«1-10»

class SemiGroup (G : Type) : Type
  extends
    Mul G
where
  mul_assoc (a b c : G) : a * b * c = a * (b * c)

namespace a

variable {A : Type} [SemiGroup A]
variable {e : A}
variable {id_left : ∀ (a : A),  e * a = a}
variable {inv : A → A} {inv_left : ∀ (a : A), (inv a) * a = e}

include inv_left id_left in
theorem id_unic : ∀ (a : A), a * a = a → a = e := by
  intro a ha
  apply Eq.symm
  calc
    e = (inv a) * a := Eq.symm (inv_left a)
    _ = (inv a) * (a * a) := by rw [ha]
    _ = (inv a) * a * a := by rw [SemiGroup.mul_assoc]
    _ = e * a := by rw [inv_left a]
    _ = a := by rw [id_left]

include id_left inv_left in
theorem inv_right : ∀ (a : A), a * (inv a) = e := by
  intro a
  let b := inv a
  let c := inv b
  show a * b = e
  calc
    a * b
      = e * (a * b) := by rw [id_left]
    _ = (c * b) * (a * b) := by rw [inv_left]
    _ = c  * (b * a) * b := by simp [SemiGroup.mul_assoc]
    _ = c * e * b := by rw [inv_left]
    _ = c * (e * b) := by simp [SemiGroup.mul_assoc]
    _ = c * b := by rw [id_left]
    _ = e := by rw [inv_left]

include id_left inv_left in
theorem id_right : ∀ (a : A), a * e = a := by
  intro a
  let b := inv a
  have inv_right : a * b = e :=
    @inv_right A _ e id_left inv inv_left a
  calc
    a * e
      = a * (b * a) := by rw [inv_left]
    _ = a * b * a := by simp [SemiGroup.mul_assoc]
    _ = e * a := by rw [inv_right]
    _ = a := by rw [id_left]

end a
