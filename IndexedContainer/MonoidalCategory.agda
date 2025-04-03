open import Prelude
open import Cubical.Data.Unit

module IndexedContainer.MonoidalCategory {I : Type} where

open import IndexedContainer I 

module _ where
  open IndexedContainer

  idᶜ : IndexedContainer
  idᶜ .S _ = Unit
  idᶜ .P {i} _ j = i ≡ j

  module _ (F G : IndexedContainer) where
    _⊗_ : IndexedContainer
    _⊗_ .S = ⟦ G ⟧ (F .S) 
    _⊗_ .P (s , v) k = Σ[ j ∈ I ] Σ[ p ∈ G .P s j ] F .P (v p) k

  module _ {F G H K : IndexedContainer} where
    _⊗₁_ : (α : F ⇒ H) (β : G ⇒ K) → (F ⊗ G) ⇒ (H ⊗ K)
    _⊗₁_ α β _ (Gs , Gsp→Fs) .fst = 
      let 
        Ks , Ksp→Gsp = β _ Gs
      in (Ks , λ Ksp → α _ (Gsp→Fs (Ksp→Gsp Ksp)) .fst) 
    _⊗₁_ α β _ (Gs , Gsp→Fs) .snd (k , Kp , Hp) = 
      let 
        Ks , Ksp→Gsp = β _ Gs
        Gsp = Ksp→Gsp Kp
      in k , Gsp , α _ (Gsp→Fs Gsp) .snd Hp

  module _ {F F′ : IndexedContainer} where
    ⊗₁-id : id₁ F ⊗₁ id₁ F′ ≡ id₁ (F ⊗ F′)
    ⊗₁-id = refl

  module _ {F F′ G G′ H H′ : IndexedContainer}
    (α  : F ⇒ G)   (β  : G ⇒ H)
    (α′ : F′ ⇒ G′) (β′ : G′ ⇒ H′)
    where
    ⊗₁-; : (α ; β) ⊗₁ (α′ ; β′) ≡ (α ⊗₁ α′) ; (β ⊗₁ β′)
    ⊗₁-; = refl

  module _ {F G} (α : F ⇒ G) where
    record ⇒isIso : Type where
      field
        inv : G ⇒ F
        inv-l : Path (F ⇒ F) (α ; inv) (id₁ F)
        inv-r : Path (G ⇒ G) (inv ; α) (id₁ G)

module _ {F : IndexedContainer} where
  open import Cubical.Foundations.Path using (toPathP⁻; fromPathP⁻)
  open import Cubical.Data.Sigma using (ΣPathP)

  open IndexedContainer F

  unitor-l : (idᶜ ⊗ F) ⇒ F
  unitor-l _ (s , _) = s , λ p → _ , p , refl

  unitor-l-inv : F ⇒ (idᶜ ⊗ F)
  unitor-l-inv i s = (s , _) , λ { (k , p , k≡j) → subst (P s) k≡j p }

  unitor-l-inv-l : Path ((idᶜ ⊗ F) ⇒ (idᶜ ⊗ F)) (unitor-l ; unitor-l-inv) (id₁ (idᶜ ⊗ F))
  unitor-l-inv-l =
    ⇒PathP λ { _ (s , _) → ΣPathP
      ( ΣPathP (refl , refl) 
      , implicitFunExt λ {j} →
        funExt λ { (k , p , k≡j) → ΣPathP
          ( sym k≡j
          , ΣPathP
            ( symP (subst-filler (P s) k≡j p)
            , symP λ ι κ → k≡j (ι ∨ κ)
            )
          )
        }
      )
    }

  unitor-r : (F ⊗ idᶜ) ⇒ F
  unitor-r _ (_ , si) .fst = si refl
  unitor-r i (_ , si) .snd p = i , refl , p

  unitor-r-inv : F ⇒ (F ⊗ idᶜ) 
  unitor-r-inv _ s .fst = _ , λ i≡j → subst S i≡j s
  unitor-r-inv i s .snd {j} (k , i≡k , p) = 
    transport P≡ p
    where
    P≡ : P {k} (subst S i≡k s) j ≡ P {i} s j
    P≡ = cong₂ (λ i s → P {i} s j) (sym i≡k) (symP (subst-filler S i≡k s))
    -- -- In a perfect world this would be:
    -- J
    --   (λ h i≡h → P (subst S i≡h s) j → P s j)
    --   (substP F (substRefl {B = S} s))
    --   i≡k
    --   p
    -- -- But this is not a perfect world.

module _ {F G H : IndexedContainer} where
  associator : (F ⊗ (G ⊗ H)) ⇒ ((F ⊗ G) ⊗ H)
  associator _ ((s″ , op″) , op′) .fst  = s″ , λ {j} p″ → op″ p″ , λ p′ → op′ (j , p″ , p′)
  associator _ ((s″ , op″) , op′) .snd  (k , (p″ , (j , p′ , p))) = j , (k , p″ , p′) , p

_² : IndexedContainer → IndexedContainer
IC ² = IC ⊗ IC
