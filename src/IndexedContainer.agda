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

module _ (F : IndexedContainer) where
  open IndexedContainer F
  substP : {i : I} {s s′ : S i} {j : I} (s≡s′ : s ≡ s′)  
    → P s j → P s′ j
  substP {j = j} = subst (λ s → P s j)

module _ (F : IndexedContainer) where
  open IndexedContainer F
  ⟦_⟧ : (I → Type) → (I → Type)
  ⟦_⟧ X i = Σ[ s ∈ S i ] (∀ {j} (p : P s j) → X j)

module _ (F : IndexedContainer) where
  _⟦$⟧_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ F ⟧ X i → ⟦ F ⟧ Y i)
  _⟦$⟧_ f i (s , v) = s , λ {j} p → f j (v p)

infixr 18 _⇒_ _⇒′_
_⇒_ : (F G : IndexedContainer) → Type
(S ⊲ P) ⇒ G = (i : I) (s : S i) → ⟦ G ⟧ (P s) i

_⇒′_ : (F G : IndexedContainer) → Type
(S ⊲ P) ⇒′ (S′ ⊲ P′) = 
  (i : I) → Σ[ σ ∈ (S i → S′ i) ]
    (∀ s {j} → P′ (σ s) j → P s j)

module _
  {F G : IndexedContainer}
  (α : F ⇒ G) where

  ⟦⇒⟧ : (X : IType) → ⟦ F ⟧ X i→ ⟦ G ⟧ X 
  ⟦⇒⟧ X i (s , px) = let s′ , pp = α i s in s′ , pp » px

module _ {F G : IndexedContainer} {α β : F ⇒ G} where
  open IndexedContainer F

  ⇒PathP :
    (hom : (i : I) (s : S i) → α i s ≡ β i s)
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

