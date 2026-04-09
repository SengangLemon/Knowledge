import AxlerLean.AxlerSummary

namespace AxlerLean

namespace Exercises

namespace Basic

/- Problem 1 (Vector Spaces):
Show that 0 * v = 0 for every vector v.
-/
theorem p1_zero_smul_vec {n : Nat} (v : Vec n) :
    (fun i => (0 : Int) * v i) = (fun _ => (0 : Int)) := by
  funext i
  simp

/- Problem 2 (Finite-Dimensional Spaces):
If all coordinates agree, then two vectors are equal.
-/
theorem p2_vec_ext {n : Nat} {u v : Vec n} (h : ∀ i, u i = v i) : u = v := by
  funext i
  exact h i

/- Problem 3 (Linear Maps):
Identity map acts as identity.
-/
theorem p3_id_apply {n : Nat} (v : Vec n) : (LinearMap.id n).toFun v = v := by
  rfl

/- Problem 4 (Polynomials):
For f(x)=ax+b, show f(0)=b.
-/
def evalLin (a b x : Int) : Int := a * x + b

theorem p4_eval_at_zero (a b : Int) : evalLin a b 0 = b := by
  unfold evalLin
  simp

/- Problem 5 (Vector Spaces):
Show that v + 0 = v coordinatewise.
-/
theorem p5_add_zero_vec {n : Nat} (v : Vec n) :
    (fun i => v i + 0) = v := by
  funext i
  simp

/- Problem 6 (Determinants, 2x2 model):
det [[0,0],[0,0]] = 0.
-/
theorem p6_det_zero_matrix : Ch9_Determinants.det2 0 0 0 0 = 0 := by
  unfold Ch9_Determinants.det2
  simp

end Basic

namespace Standard

/- Problem 7 (Eigenvectors):
If v is an eigenvector by definition, then v is nonzero.
-/
theorem p7_eigen_nonzero {n : Nat} {T : LinearMap n n} {μ : Int} {v : Vec n}
    (h : Ch5_Eigen.IsEigenvector T μ v) : v ≠ (fun _ => 0) := h.1

/- Problem 8 (Inner Product, 2D model):
dot(0, u)=0 for the 2D dot product model.
-/
theorem p8_dot_zero_left (u : Vec 2) : Ch6_InnerProduct.dot2 (fun _ => (0 : Int)) u = 0 := by
  unfold Ch6_InnerProduct.dot2
  simp

/- Problem 9 (Operators):
Every linear map sends zero vector to zero vector.
-/
theorem p9_map_zero {n m : Nat} (T : LinearMap n m) :
    T.toFun (fun _ : Fin n => (0 : Int)) = (fun _ : Fin m => (0 : Int)) := by
  have h := T.map_smul (0 : Int) (fun _ : Fin n => (1 : Int))
  simpa using h

/- Problem 10 (Complex-like model):
Conjugation is involutive.
-/
theorem p10_conj_involutive (z : Ch8_ComplexLike.Pair) :
    Ch8_ComplexLike.conj (Ch8_ComplexLike.conj z) = z := by
  cases z
  simp [Ch8_ComplexLike.conj]

/- Problem 11 (Linear Maps):
Composition with identity on the right gives the same map.
-/
theorem p11_comp_id_right {n m : Nat} (f : LinearMap n m) :
    LinearMap.comp f (LinearMap.id n) = f := by
  exact LinearMap.comp_id_right f

/- Problem 12 (Polynomials):
For f(x)=ax+b, show f(1)=a+b.
-/
theorem p12_eval_at_one (a b : Int) : Basic.evalLin a b 1 = a + b := by
  unfold Basic.evalLin
  simp

end Standard

namespace Challenge

/- Problem 13 (Linear Maps):
Composition with identity on the left gives the same map.
-/
theorem p13_comp_id_left {n m : Nat} (f : LinearMap n m) :
    LinearMap.comp (LinearMap.id m) f = f := by
  exact LinearMap.comp_id_left f

/- Problem 14 (Linear Maps):
Associativity of composition.
-/
theorem p14_comp_assoc {n m k l : Nat}
    (h : LinearMap k l) (g : LinearMap m k) (f : LinearMap n m) :
    LinearMap.comp h (LinearMap.comp g f) = LinearMap.comp (LinearMap.comp h g) f := by
  exact LinearMap.comp_assoc h g f

/- Problem 15 (Finite-Dimensional Spaces):
If all coordinates are zero, then the vector is zero.
-/
theorem p15_vec_zero_unique {n : Nat} {v : Vec n}
    (h : ∀ i, v i = 0) : v = (fun _ => (0 : Int)) := by
  funext i
  exact h i

/- Problem 16 (Inner Product, 2D model):
dot(u,v)=dot(v,u) for the 2D model.
-/
theorem p16_dot_comm (u v : Vec 2) :
    Ch6_InnerProduct.dot2 u v = Ch6_InnerProduct.dot2 v u := by
  exact Ch6_InnerProduct.dot2_comm u v

/- Problem 17 (Determinants, 2x2 model):
Equal rows imply zero determinant.
-/
theorem p17_det_equal_rows (a b : Int) :
    Ch9_Determinants.det2 a b a b = 0 := by
  exact Ch9_Determinants.det2_zero_of_equal_rows a b

/- Problem 18 (Complex-like model):
Real part is fixed under conjugation.
-/
theorem p18_conj_re_fixed (z : Ch8_ComplexLike.Pair) :
    (Ch8_ComplexLike.conj z).re = z.re := by
  exact Ch8_ComplexLike.conj_re_fixed z

end Challenge

end Exercises
end AxlerLean
