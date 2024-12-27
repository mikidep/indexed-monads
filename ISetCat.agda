open import Prelude
open import Cubical.WildCat.Base
open import WildCat.Functor

module ISetCat (I : Type) where

open import Definitions I
open WildCat

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

module _ {F G : ISetEndo} {α β : ISetEndoTrans F G}
         where
  open WildNatTrans
  open WildFunctor

  ISetEndoTransPathP : (N-ob≡ : α .N-ob ≡ β .N-ob) → α ≡ β
  ISetEndoTransPathP N-ob≡ = WildNatTransPathP
    N-ob≡
    λ {X} {Y} f → toPathP (isSetΠ2 (λ i _ → G .F-ob Y i .snd) _ _ _ _)
    where
    open import Cubical.Foundations.HLevels

module _ where
  open import Cubical.Functions.FunExtEquiv using (funExt₂; funExt₂Equiv)
  open import Cubical.Foundations.Equiv using (invEq)
  open WildNatTrans

  ISetEndoCat : WildCat (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
  ISetEndoCat .ob = ISetEndo
  ISetEndoCat .Hom[_,_] = ISetEndoTrans
  ISetEndoCat .id {x = F} .N-ob τ = λ i x → x
  ISetEndoCat .id {x = F} .N-hom f = refl
  ISetEndoCat ._⋆_ α β .N-ob τ i = α .N-ob τ i » β .N-ob τ i
  ISetEndoCat ._⋆_ α β .N-hom f =
    funExt₂ λ i x →
      cong (β .N-ob _ i) (invEq funExt₂Equiv (α .N-hom f) i x)
      ∙ invEq funExt₂Equiv (β .N-hom f) i (α .N-ob _ i x)
  ISetEndoCat .⋆IdL α       = ISetEndoTransPathP refl
  ISetEndoCat .⋆IdR α       = ISetEndoTransPathP refl
  ISetEndoCat .⋆Assoc α β γ = ISetEndoTransPathP refl

