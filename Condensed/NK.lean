import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Condensed.Basic


open CategoryTheory AlgebraicGeometry

/-
1. What is the notion of Grothendieck Topology formalized here
2. What is a covering Sieve? (OK)
3. What is condition `CoverDense`
-/

/-
1.Answer: A Grothendieck Topology is a `Category` with extra structure: Namely,
  1.  A collection of 'covering' sieves `J X` on each object, such that
    i) Maximal sieve is in `J X`
    ii) Stable under pullbacks
    iii) A sieve `R` on `X` is in `J X`, if and only if it is so locally, i.e. if
        H: There is `S ∈ J X`, such that for each `f: Y ⟶ X` in `S`, we have `f⁻¹ R ∈ J Y`, then
        C: `R ∈ J X`
-/
def SchemesOver (X : Scheme) := (Y : Scheme) → (Y ⟶ X)


-- def bigEtale: GrothendieckTopology Scheme where
--   sieves X := {R : Sieve X | ∃ (n: ℕ) (ι: range n → R) , (∀ i : range n, etale (ι n))  }
--   top_mem' := by simp only [Set.setOf_true, Set.mem_univ, forall_const]
--   pullback_stable' := by simp only [Set.setOf_true, Set.mem_univ, forall_true_left, implies_true, forall_const]
--   transitive' := by simp only [Set.setOf_true, Set.mem_univ, implies_true, forall_const, forall_true_left]

-- #check GrothendieckTopology
-- #check Π x : ℕ, range n

/-Answer to 3.
We need a Functor `G: C ⥤ D` and a Grothendieck topology `K` on `D`. Then `CoverDense K D` states:
1. For each object `X ` of `D`,  such that:
 i) `Sieve.coverByImage G X ∈ GrothendieckTopology.sieves K X`.
 This states that the specific sieve
 `Sieve.coverByImage G X` is a covering Sieve for `K`. This Sieve is defined as the collection of all
  arrows that factor through an image object (!) `G.obj Y` of `G`.
 Equivalently, there exists a covering sieve `R : K.sieves X`, such that
 i')
-/

#check CoverDense.is_cover
#check Sieve.coverByImage


/-Question: How does this apply to CompactHausd/ Extremally disc. spaces?-/
-- What are the coverings in CompactHausd even?
-- It seems that `CompHaus` has the "coherent" topology, which makes sense for categories `C`
-- satisfying `Precoherent C`
#check coherentTopology