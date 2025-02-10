open import Prelude

open import Cubical.Foundations.Function using (idfun)
open import Cubical.Functions.FunExtEquiv using (funExt₂; funExtDep)
open import Cubical.Data.Unit

module IndexedContainer (I : Type) where

open import Definitions I

record IndexedContainer  : Type₁ where
  field
    S : (i : I) → Type
    P : {i : I} → S i → (j : I) → Type

module _ where
  open IndexedContainer

  substP : (F : IndexedContainer) {i : I} {s s′ : F .S i} {j : I} (s≡s′ : s ≡ s′)  
    → F .P s j → F .P s′ j
  substP F {j = j} = subst (λ s → F .P s j)

  record _Π⇒_ (F G : IndexedContainer) {i : I} (s : F .S i) : Type where
    field
      σs : G .S i
      πs : ∀ {j} → G .P σs j → F .P s j

  open _Π⇒_ public

  module _ {F G : IndexedContainer} {i : I} {s : F .S i} where
    open import Cubical.Foundations.Isomorphism
    open Iso

    Π⇒IsoΣ : Iso ((F Π⇒ G) s) (Σ (G .S i) (λ σs → ∀ {j} → G .P σs j → F .P s j))
    Π⇒IsoΣ .fun x = x .σs , x .πs
    Π⇒IsoΣ .inv (σs , πs) = record { σs = σs ; πs = πs }
    Π⇒IsoΣ .rightInv _ = refl
    Π⇒IsoΣ .leftInv _ = refl

  module _ {F G : IndexedContainer} {i : I} {s : F .S i} {α β : (F Π⇒ G) s} where
    Π⇒PathP : 
      (≡σs : α .σs ≡ β .σs)
      (≡πs : PathP {ℓ-zero} (λ ι → ∀ {j} → G .P (≡σs ι) j → F .P s j) (α .πs) (β .πs))
      → α ≡ β
    Π⇒PathP ≡σs ≡πs ι .σs = ≡σs ι
    Π⇒PathP ≡σs ≡πs ι .πs = ≡πs ι

  _⇒_ : (F G : IndexedContainer) → Type
  F ⇒ G = (i : I) (s : F .S i) → (F Π⇒ G) s

  module _ {F G : IndexedContainer} {α β : F ⇒ G} where
    ⇒PathP :
      (Π≡ : {i : I} (s : F .S i) → α i s ≡ β i s)
      → α ≡ β
    ⇒PathP Π≡ ι i s = Π≡ s ι

  module _ {F G : IndexedContainer} {α β : F ⇒ G} (α≡β : α ≡ β) where
    σs≡ : {i : I} (s : F .S i) → α i s .σs ≡ β i s .σs
    σs≡ s ι = α≡β ι _ s .σs

    πs≡ : {i : I} (s : F .S i) {j : I}
      → PathP {ℓ-zero} (λ ι → G .P (σs≡ s ι) j → F .P s j) (α i s .πs) (β i s .πs)
    πs≡ s ι = α≡β ι _ s .πs

  module _ (F : IndexedContainer) where
    id₁ : F ⇒ F 
    id₁ _ s .σs = s
    id₁ _ s .πs = idfun _

  module _ (F : IndexedContainer) where
    ⟦_⟧ : (I → Type) → (I → Type)
    ⟦_⟧ X i = Σ[ s ∈ F .S i ] (∀ {j} (p : F .P s j) → X j)

  module _ (F : IndexedContainer) where
    _⟦$⟧_ : {X Y : I → Type} → (∀ i → X i → Y i) → (∀ i → ⟦ F ⟧ X i → ⟦ F ⟧ Y i)
    _⟦$⟧_ f i (s , v) = s , λ {j} p → f j (v p)

  module _
    {F G : IndexedContainer}
    (α : F ⇒ G) where

   ⟦⇒⟧ : (X : IType) → ⟦ F ⟧ X i→ ⟦ G ⟧ X 
   ⟦⇒⟧ X i (s , v) = α i s .σs , α i s .πs » v

module _ {F G H : IndexedContainer} where
  infixl 20 _;_
  _;_ : (α : F ⇒ G) (β : G ⇒ H) → (F ⇒ H)
  (α ; β) _ s .σs   = β _ (α _ s .σs) .σs 
  (α ; β) _ s .πs p = α _ s .πs (β _ (α _ s .σs) .πs p)


