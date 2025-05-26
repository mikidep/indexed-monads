open import Prelude

open import Cubical.Foundations.Function using (idfun)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)
open import Cubical.Data.Unit

module IndexedContainer (I : Type) where

open import Definitions I

infix 19 _⊲_
record IndexedContainer  : Type₁ where
  constructor _⊲_
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

open IndexedContainer

substP : (F : IndexedContainer) {i : I} {s s′ : F .S i} {j : I} (s≡s′ : s ≡ s′)  
  → F .P s j → F .P s′ j
substP F {j = j} = subst (λ s → F .P s j)

module _ {F G : IndexedContainer} {i : I} {s : F .S i} where
  open import Cubical.Foundations.Isomorphism
  open Iso

module _ (F : IndexedContainer) where
  ⟦_⟧ : (I → Type) → (I → Type)
  ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)

module _ (F : IndexedContainer) where
  _⟦$⟧_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ F ⟧ X i → ⟦ F ⟧ Y i)
  _⟦$⟧_ f i (s , v) = s , λ {j} p → f j (v p)

infixr 18 _⇒_
_⇒_ : (F G : IndexedContainer) → Type
F ⇒ G = (i : I) (s : F .S i) → ⟦ G ⟧ (F .P s) i

module _
  {F G : IndexedContainer}
  (α : F ⇒ G) where

  ⟦⇒⟧ : (X : IType) → ⟦ F ⟧ X i→ ⟦ G ⟧ X 
  ⟦⇒⟧ X i (s , px) = let s′ , pp = α i s in s′ , pp » px

module _ {F G : IndexedContainer} {α β : F ⇒ G} where
  ⇒PathP :
    (hom : (i : I) (s : F .S i) → α i s ≡ β i s)
    → Path (F ⇒ G) α β
  ⇒PathP hom = funExt₂ hom

module _ (F : IndexedContainer) where
  id₁ : F ⇒ F 
  id₁ _ s = (s , idfun _)

module _ {F G H : IndexedContainer} where
  infixl 20 _;_
  _;_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  _;_ α β i s = let
      s′ , v′ = α i s
      s″ , v″ = β i s′
    in s″ , v″ » v′

