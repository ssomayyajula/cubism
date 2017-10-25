{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Agda.Primitive.Cubical 
open import Data.Product
open import Function

infix 30 ~
~ = primINeg

infixr 20 _∧_ _∨_
_∧_ = primIMin
_∨_ = primIMax

postulate
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ
{-# BUILTIN PATHP PathP #-}

_==_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_==_ {A = A} = PathP (λ _ → A)

module _ {ℓ} {A : Set ℓ} {x : A} where
  -- 3.1
  refl : x == x
  refl _ = x

  isContr-Singleton-lem : {y : A} (p : x == y) → (x , refl) == (y , p)
  isContr-Singleton-lem p i = p i , λ j → p (i ∧ j)

-- TAKEN FROM SAIZAN
transp : {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) → P i0 → P i1
transp P ai0 = primComp P i0 (λ x → isOneEmpty) ai0

module _ {ℓ} {A : Set ℓ} {x : A} where
  -- TAKEN FROM SAIZAN
  J : ∀ {ℓ'} (P : (y : A) → x == y → Set ℓ') → P x refl → {y : A} (p : x == y) → P y p
  J P r p = transp (λ i → uncurry P $ isContr-Singleton-lem p i) r

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = Σ A (λ x → (y : A) → x == y)

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) where
  fiber : (y : B) → Set (ℓ₁ ⊔ ℓ₂)
  fiber y = Σ A (λ x → y == f x)

isEquiv : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → (A → B) → Set (ℓ₁ ⊔ ℓ₂)
isEquiv _ B f = (y : B) → isContr (fiber f y)

{-# BUILTIN ISEQUIV isEquiv #-}

infix 4 _≃_
_≃_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A ≃ B = Σ (A → B) (isEquiv A B)

ide : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ide = id , λ y → (y , refl) , isContr-Singleton-lem ∘ proj₂

primitive
  primGlue : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (φ : I)
    → (T : Partial (Set ℓ₂) φ) → (f : PartialP φ (λ o → T o → A))
    → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set ℓ₂

-- TAKEN FROM SAIZAN
Glue : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) → (φ : I) → (T : Partial (Set ℓ₂) φ)
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ₂
Glue A φ T f = primGlue A φ T (λ o → proj₁ $ f o) (λ o → proj₂ $ f o)

-- TAKEN FROM SAIZAN
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A == B
ua {A = A} {B} f i = Glue B (~ i ∨ i)
  (λ {(i = i0) → A ; (i = i1) → B})
  (λ {(i = i0) → f ; (i = i1) → ide})

open import Data.Bool

coe : ∀ {ℓ₁} {A B : Set ℓ₁} → A == B → A → B
coe {A = A} {B} p = J (λ B _ → A → B) id p

id-ua : Bool → Bool
id-ua = coe $ ua ide
