import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

universe v₁ v₂ u₁ u₂
namespace CategoryTheory
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₁} [Category.{v₁} C]
open Limits

-- Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
/--
A Cofork diagram which has a splitting (in the sense of `IsSplitCoequalizer`) is colimiting.
This lemma is an unbundeling of `IsSplitCoequalizer.isCoequalizer`
-/
def Cofork.IsColimit.ofSplitting {A B : C} {f g : A ⟶ B} (c : Cofork f g)
    (s : c.pt ⟶ B) (hs : s ≫ c.π = 𝟙 _) (t : B ⟶ A) (htf : t ≫ f = 𝟙 _) (htg : t ≫ g = c.π ≫ s) :
    IsColimit c := by
  refine Cofork.IsColimit.mk' _ (fun c' => ⟨s ≫ c'.π,
    by rw [← reassoc_of% htg, ← c'.condition, reassoc_of% htf],
    fun {m} hm => by dsimp at m; rw [← Category.id_comp m,← hs,Category.assoc,hm]⟩)


end CategoryTheory
