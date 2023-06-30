import ExtrDisc.Basic

universe u

open CategoryTheory CategoryTheory.Limits ExtrDisc

lemma toCompHausPreservesFiniteCoproducts : PreservesFiniteCoproducts toCompHaus := by
  sorry 

lemma DagurOpenEmbedding {α : Type} [Fintype α] (Z : α → ExtrDisc.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  constructor
  · sorry
  · sorry