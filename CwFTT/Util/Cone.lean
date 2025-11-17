import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

universe v₁ v₂ u₁ u₂
namespace CategoryTheory
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₁} [Category.{v₁} C]
open Limits

def Cofork.IsColimit.ofSplitting {A B : C} {f g : A ⟶ B} (c : Cofork f g)
    (s : c.pt ⟶ B) (hs : s ≫ c.π = 𝟙 _) (t : B ⟶ A) (htf : t ≫ f = 𝟙 _) (htg : t ≫ g = c.π ≫ s) :
    IsColimit c := by
  refine Cofork.IsColimit.mk _ ?_ ?_ ?_
  · intro c'
    exact s ≫ c'.π
  · intro c'
    rw [← reassoc_of% htg,← c'.condition,reassoc_of% htf]
  · intro c' m hm
    rw [← Category.id_comp m,← hs,Category.assoc,hm]


end CategoryTheory
