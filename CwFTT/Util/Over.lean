import Mathlib.CategoryTheory.Comma.Over.Basic

universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open Limits -- possibly unneeded
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

def Over.natTrans (X : C) : Over.forget X ⟶ (Functor.const _).obj X where
  app Y := Y.hom

def Over.liftForget (X : C) : Over.lift (Over.forget X) (Over.natTrans X) ≅ 𝟭 (Over X) :=
  Iso.refl _

def Over.liftCompForgetIso (X : D) (F : C ⥤ D) (f : F ⟶ (Functor.const _).obj X) :
  Over.lift F f ⋙ Over.forget _ ≅ F := Iso.refl _

def Over.lift₂ {F G : C ⥤ D} (η : F ⟶ G) {X : D} (g : G ⟶ (Functor.const _).obj X) :
    Over.lift F (η ≫ g) ⟶ Over.lift G g where
  app Y := Over.homMk (η.app Y)

lemma whiskerLeft_forgetTrans (F : C ⥤ D) {X : D} (f : F ⟶ (Functor.const C).obj X) :
  (Over.lift F f).whiskerLeft (Over.natTrans X) =
  (Over.liftCompForgetIso _ _ _).hom ≫ f := by
  ext
  simp [Over.natTrans,Over.liftCompForgetIso]

-- lemma Over.liftAdj

end CategoryTheory
