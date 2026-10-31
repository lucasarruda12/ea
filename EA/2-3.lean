/- Eu gosto muito mais da definição mais cheia de homomorfismo.
A que diz que tem que respeitar tudo: operação, identidade e inversos.
-/

import EA.«1-10»

namespace criterion

variable (G H : Type) [Group G] [Group H]
variable (f : G → H)
variable (f_op : ∀a b : G, f (a * b) = f a * f b)

include f f_op in
theorem f_id : f 1 = 1 := by
  have this : f 1 * f 1 = f 1 := by
    apply Eq.symm
    calc
      f 1
        = f (1 * 1) := by
        rw [Group.one_mul 1]
      _ = f 1 * f 1 := by
        rw [f_op]

  exact ex10.invol H (f 1) this

include f f_op in
theorem f_inv (g : G) : f (g⁻¹) = (f g)⁻¹ := by
  rw [← Group.mul_one (f g)⁻¹]
  apply ex10.res_unic_right
  rw [← f_op, Group.mul_inv]
  exact (f_id G H f f_op)

end criterion
