open import Prelude
open import Cubical.WildCat.Base
open import WildCat.Functor

module ISetCat (I : Type) where

open import Definitions I
open WildCat
open WildFunctor
open WildNatTrans

ISetCat : WildCat (ℓ-suc ℓ-zero) ℓ-zero
ISetCat .ob = ISet
ISetCat .Hom[_,_] X Y = X is→ Y
ISetCat .id = λ i x → x
ISetCat ._⋆_ f g i = f i » g i
ISetCat .⋆IdL _ = refl
ISetCat .⋆IdR _ = refl
ISetCat .⋆Assoc _ _ _ = refl

ISetEndo = WildFunctor ISetCat ISetCat
ISetEndoTrans = WildNatTrans ISetCat ISetCat

IdEndo : ISetEndo
IdEndo .F-ob = idfun _ 
IdEndo .F-hom = idfun _
IdEndo .F-id = refl
IdEndo .F-seq _ _ = refl

module _ (F G : ISetEndo) where
  CompEndo : ISetEndo
  CompEndo .F-ob = F .F-ob » G .F-ob
  CompEndo .F-hom = F .F-hom » G .F-hom
  CompEndo .F-id = cong (G .F-hom) (F .F-id) ∙ G .F-id 
  CompEndo .F-seq f g = cong (G .F-hom) (F .F-seq f g) ∙ G .F-seq (F .F-hom f) (F .F-hom g)

infixl 15 _;E_
_;E_ = CompEndo

module _ {F G : ISetEndo} where
  _⊲_ :
    (L : ISetEndo)
    (α : ISetEndoTrans F G) 
    → ISetEndoTrans (L ;E F) (L ;E G)
  (L ⊲ α) .N-ob X  = α .N-ob (L .F-ob X)
  (L ⊲ α) .N-hom f = α .N-hom (L .F-hom f)

  _⊳_ : 
    (α : ISetEndoTrans F G) 
    (R : ISetEndo)
    → ISetEndoTrans (F ;E R) (G ;E R)
  (α ⊳ R) .N-ob X  = R .F-hom (α .N-ob X)
  (α ⊳ R) .N-hom f =
      sym (R .F-seq (F .F-hom f) (α .N-ob _))
    ∙ cong (R .F-hom) (α .N-hom f)
    ∙ R .F-seq (α .N-ob _) _

module _ (F : ISetEndo) where
  ISetIdTrans : ISetEndoTrans F F
  ISetIdTrans .N-ob τ = λ i x → x
  ISetIdTrans .N-hom f = refl

  ISEUnitorLInv : ISetEndoTrans F (IdEndo ;E F)
  ISEUnitorLInv .N-ob X i = {! ciaoo  !}
  ISEUnitorLInv .N-hom = {! !}

module _ {F G : ISetEndo} {α β : ISetEndoTrans F G} where
  ISetEndoTransPathP : (N-ob≡ : α .N-ob ≡ β .N-ob) → α ≡ β
  ISetEndoTransPathP N-ob≡ = WildNatTransPathP
    N-ob≡
    λ {X} {Y} f → toPathP (isSetΠ2 (λ i _ → G .F-ob Y i .snd) _ _ _ _)
    where
    open import Cubical.Foundations.HLevels

module _ where
  open import Cubical.Functions.FunExtEquiv using (funExt₂; funExt₂Equiv)
  open import Cubical.Foundations.Equiv using (invEq)

  ISetEndoCat : WildCat (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
  ISetEndoCat .ob = ISetEndo
  ISetEndoCat .Hom[_,_] = ISetEndoTrans
  ISetEndoCat .id {x = F} = ISetIdTrans F
  ISetEndoCat ._⋆_ α β .N-ob τ i = α .N-ob τ i » β .N-ob τ i
  ISetEndoCat ._⋆_ α β .N-hom f =
    funExt₂ λ i x →
      cong (β .N-ob _ i) (invEq funExt₂Equiv (α .N-hom f) i x)
      ∙ invEq funExt₂Equiv (β .N-hom f) i (α .N-ob _ i x)
  ISetEndoCat .⋆IdL α       = ISetEndoTransPathP refl
  ISetEndoCat .⋆IdR α       = ISetEndoTransPathP refl
  ISetEndoCat .⋆Assoc α β γ = ISetEndoTransPathP refl

