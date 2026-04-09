namespace AxlerLean

abbrev Vec (n : Nat) := Fin n -> Int

structure LinearMap (n m : Nat) where
  toFun : Vec n -> Vec m
  map_add : ∀ u v, toFun (fun i => u i + v i) = fun j => toFun u j + toFun v j
  map_smul : ∀ (a : Int) u, toFun (fun i => a * u i) = fun j => a * toFun u j

namespace LinearMap

def id (n : Nat) : LinearMap n n where
  toFun := fun v => v
  map_add := by intro u v; rfl
  map_smul := by intro a u; rfl

def comp {n m k : Nat} (g : LinearMap m k) (f : LinearMap n m) : LinearMap n k where
  toFun := fun v => g.toFun (f.toFun v)
  map_add := by
    intro u v
    calc
      g.toFun (f.toFun (fun i => u i + v i))
          = g.toFun (fun j => f.toFun u j + f.toFun v j) := by rw [f.map_add]
      _ = fun t => g.toFun (f.toFun u) t + g.toFun (f.toFun v) t := by rw [g.map_add]
  map_smul := by
    intro a u
    calc
      g.toFun (f.toFun (fun i => a * u i))
          = g.toFun (fun j => a * f.toFun u j) := by rw [f.map_smul]
      _ = fun t => a * g.toFun (f.toFun u) t := by rw [g.map_smul]

theorem comp_assoc {n m k l : Nat}
    (h : LinearMap k l) (g : LinearMap m k) (f : LinearMap n m) :
    comp h (comp g f) = comp (comp h g) f := by
  rfl

theorem comp_id_left {n m : Nat} (f : LinearMap n m) :
    comp (id m) f = f := by
  cases f
  rfl

theorem comp_id_right {n m : Nat} (f : LinearMap n m) :
    comp f (id n) = f := by
  cases f
  rfl

end LinearMap

/- Axler chapter-aligned minimal formal notes -/
namespace Ch1_VectorSpaces

theorem zero_smul_vec {n : Nat} (v : Vec n) :
    (fun i => (0 : Int) * v i) = (fun _ => (0 : Int)) := by
  funext i
  simp

theorem add_zero_vec {n : Nat} (v : Vec n) :
    (fun i => v i + 0) = v := by
  funext i
  simp

theorem neg_add_vec {n : Nat} (v : Vec n) :
    (fun i => v i + (-v i)) = (fun _ => (0 : Int)) := by
  funext i
  exact Int.add_right_neg (v i)

end Ch1_VectorSpaces

namespace Ch2_FiniteDim

theorem vec_ext {n : Nat} {u v : Vec n} (h : ∀ i, u i = v i) : u = v := by
  funext i
  exact h i

theorem vec_eq_of_all_coords_eq {n : Nat} {u v : Vec n}
    (h : ∀ i : Fin n, u i = v i) : u = v := by
  exact vec_ext h

theorem vec_zero_unique {n : Nat} {v : Vec n}
    (h : ∀ i, v i = 0) : v = (fun _ => (0 : Int)) := by
  funext i
  exact h i

end Ch2_FiniteDim

namespace Ch3_LinearMaps

open LinearMap

theorem id_apply {n : Nat} (v : Vec n) : (LinearMap.id n).toFun v = v := by
  rfl

theorem comp_apply {n m k : Nat} (g : LinearMap m k) (f : LinearMap n m) (v : Vec n) :
    (comp g f).toFun v = g.toFun (f.toFun v) := by
  rfl

theorem comp_preserves_smul {n m k : Nat}
    (g : LinearMap m k) (f : LinearMap n m) (a : Int) (v : Vec n) :
    (comp g f).toFun (fun i => a * v i) = fun j => a * (comp g f).toFun v j := by
  exact (comp g f).map_smul a v

end Ch3_LinearMaps

namespace Ch4_Polynomials

def evalLin (a b x : Int) : Int := a * x + b

theorem evalLin_at_zero (a b : Int) : evalLin a b 0 = b := by
  unfold evalLin
  simp

theorem evalLin_one (a b : Int) :
    evalLin a b 1 = a + b := by
  unfold evalLin
  simp

end Ch4_Polynomials

namespace Ch5_Eigen

def IsEigenvector {n : Nat} (T : LinearMap n n) (μ : Int) (v : Vec n) : Prop :=
  v ≠ (fun _ => 0) ∧ T.toFun v = (fun i => μ * v i)

theorem eigenvector_nonzero {n : Nat} {T : LinearMap n n} {μ : Int} {v : Vec n}
    (h : IsEigenvector T μ v) : v ≠ (fun _ => 0) := h.1

theorem eigenvector_eq_scale {n : Nat} {T : LinearMap n n} {μ : Int} {v : Vec n}
    (h : IsEigenvector T μ v) :
    T.toFun v = (fun i => μ * v i) := h.2

end Ch5_Eigen

namespace Ch6_InnerProduct

def dot2 (u v : Vec 2) : Int := u ⟨0, by decide⟩ * v ⟨0, by decide⟩ + u ⟨1, by decide⟩ * v ⟨1, by decide⟩

theorem dot2_comm (u v : Vec 2) : dot2 u v = dot2 v u := by
  unfold dot2
  calc
    u ⟨0, by decide⟩ * v ⟨0, by decide⟩ + u ⟨1, by decide⟩ * v ⟨1, by decide⟩
        = v ⟨0, by decide⟩ * u ⟨0, by decide⟩ + v ⟨1, by decide⟩ * u ⟨1, by decide⟩ := by
            rw [Int.mul_comm (u ⟨0, by decide⟩) (v ⟨0, by decide⟩),
              Int.mul_comm (u ⟨1, by decide⟩) (v ⟨1, by decide⟩)]

theorem dot2_zero_left (u : Vec 2) : dot2 (fun _ => (0 : Int)) u = 0 := by
  unfold dot2
  simp

end Ch6_InnerProduct

namespace Ch7_Operators

open LinearMap

theorem op_preserves_add {n m : Nat} (T : LinearMap n m) (u v : Vec n) :
    T.toFun (fun i => u i + v i) = fun j => T.toFun u j + T.toFun v j := by
  exact T.map_add u v

theorem op_preserves_zero {n m : Nat} (T : LinearMap n m) :
    T.toFun (fun _ : Fin n => (0 : Int)) = (fun _ : Fin m => (0 : Int)) := by
  have h := T.map_smul (0 : Int) (fun _ : Fin n => (1 : Int))
  simpa using h

end Ch7_Operators

namespace Ch8_ComplexLike

structure Pair where
  re : Int
  im : Int

def conj (z : Pair) : Pair := { re := z.re, im := -z.im }

theorem conj_involutive (z : Pair) : conj (conj z) = z := by
  cases z
  simp [conj]

theorem conj_re_fixed (z : Pair) : (conj z).re = z.re := by
  rfl

end Ch8_ComplexLike

namespace Ch9_Determinants

def det2 (a b c d : Int) : Int := a * d - b * c

theorem det2_zero_of_equal_rows (a b : Int) : det2 a b a b = 0 := by
  unfold det2
  calc
    a * b - b * a = a * b - a * b := by rw [Int.mul_comm b a]
    _ = 0 := by simp

theorem det2_zero_matrix : det2 0 0 0 0 = 0 := by
  unfold det2
  simp

end Ch9_Determinants

end AxlerLean
