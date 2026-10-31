class Monoid (M : Type) : Type
  extends
    Mul M, One M
where
  mul_assoc (a b c : M) : a * b * c = a * (b * c)
  one_mul (a : M) : 1 * a = a
  mul_one (a : M) : a * 1 = a

@[ext]
structure AddNat : Type where
  val : Nat

instance  : Monoid AddNat where
  mul x y := ⟨x.val + y.val⟩
  one := ⟨0⟩
  mul_assoc a b c := by
    ext
    exact Nat.add_assoc a.val b.val c.val
  one_mul a := by
    ext
    exact Nat.zero_add a.val
  mul_one a := by
    ext
    exact Nat.add_zero a.val

@[ext]
structure MulNat : Type where
  val : Nat

instance : Monoid MulNat where
  mul a b := ⟨a.val * b.val⟩
  one := ⟨1⟩
  mul_assoc a b c := by
    ext
    exact Nat.mul_assoc a.val b.val c.val
  one_mul a := by
    ext
    exact Nat.one_mul a.val
  mul_one a := by
    ext
    exact Nat.mul_one a.val

structure MonHom (M : Type) (N : Type) [Monoid M] [Monoid N] : Type where
  f : M → N
  f_mul : ∀ a b : M, f (a * b) = f a * f b
  f_one : f 1 = 1

def f : MonHom AddNat MulNat where
  f n := ⟨2 ^ n.val⟩
  f_mul := by
    intro ⟨a⟩ ⟨b⟩
    ext; simp
    exact Nat.pow_add 2 a b

  f_one := by
    ext; rfl

theorem f_mono : ∀ a b : AddNat, f.f a = f.f b → a = b := by
  intro ⟨a⟩ ⟨b⟩ h
  ext;simp
  injection h with h'
  have this := @Nat.pow_right_inj 2 a b (by decide)
  apply this.mp
  exact h'

-- E não é epimorfismo :P. Tome como contraexemplo o (3 : MulNat)
