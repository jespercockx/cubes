{-# OPTIONS --rewriting #-}

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

Π : ∀ {ℓ ℓ′} (A : Set ℓ) (B : A → Set ℓ′) → Set _
Π A B = (x : A) → B x

infix 0 _↦_
infix 1 _$_
infixl 5 _∘_
infix 10 _─_

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

postulate
  I        : Set
  ₀ ₁      : I
  _[_-_]   : I → I → I → I

data _─_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  path : (M : I → A) → M ₀ ─ M ₁

_$_ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ─ b → I → A
path M $ i = M i

postulate
  coerce   : ∀ {ℓ} {S T : Set ℓ} (Q : S ─ T) (p q : I) → Q $ p → Q $ q
  _∘_      : ∀ {ℓ} {S T U : Set ℓ} → S ─ T → T ─ U → S ─ U

infixr 20 coerce
syntax coerce Q p q a = a [ p ∣ Q ∣ q ⟩

infix 2 path
syntax path (λ i → t) = ⟨ i ⟩ t

postulate
  [-]-left   : ∀ q r → ₀ [ q - r ] ↦ q
  [-]-right  : ∀ q r → ₁ [ q - r ] ↦ r
  coerce-0-0 : ∀ ℓ (S T : Set ℓ) (Q : S ─ T) a → a [ ₀ ∣ Q ∣ ₀ ⟩ ↦ a
  coerce-1-1 : ∀ ℓ (S T : Set ℓ) (Q : S ─ T) a → a [ ₁ ∣ Q ∣ ₁ ⟩ ↦ a
  $-₀        : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ─ T) → Q $ ₀ ↦ S
  $-₁        : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ─ T) → Q $ ₁ ↦ T

{-# REWRITE [-]-left   #-}
{-# REWRITE [-]-right  #-}
{-# REWRITE coerce-0-0 #-}
{-# REWRITE coerce-1-1 #-}
{-# REWRITE $-₀        #-}
{-# REWRITE $-₁        #-}

postulate
  [₀-₀]      : ∀ p → p [ ₀ - ₀ ] ↦ ₀
  [₀-₁]      : ∀ p → p [ ₀ - ₁ ] ↦ p
  [₁-₁]      : ∀ p → p [ ₁ - ₁ ] ↦ ₁
  path-η     : ∀ ℓ (A : Set ℓ) (S T : A) (Q : S ─ T) → ⟨ i ⟩ (Q $ i) ↦ Q

{-# REWRITE [₀-₀]  #-}
{-# REWRITE [₀-₁]  #-}
{-# REWRITE [₁-₁]  #-}
{-# REWRITE path-η #-}

postulate
  coerce-const : ∀ ℓ (A : Set ℓ) a p q → a [ p ∣ ⟨ _ ⟩ A ∣ q ⟩ ↦ a

{-# REWRITE coerce-const #-}

postulate
  coerce-∘   : ∀ ℓ (S T U : Set ℓ) (Q : S ─ T) (Q' : T ─ U) (a : S) → a [ ₀ ∣ Q ∘ Q' ∣ ₁ ⟩ ↦ ((a [ ₀ ∣ Q ∣ ₁ ⟩) [ ₀ ∣ Q' ∣ ₁ ⟩)
  coerce-∘′  : ∀ ℓ (S T U : Set ℓ) (Q : S ─ T) (Q' : T ─ U) a → a [ ₁ ∣ Q ∘ Q' ∣ ₀ ⟩ ↦ ((a [ ₁ ∣ Q' ∣ ₀ ⟩) [ ₁ ∣ Q ∣ ₀ ⟩)

  coerce-Σ   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₀) (t : T ₀ s)
             → (s , t) [ ₀ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₁ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
                   t- : (j : I) → T j (s- j)
                   t- j = t [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ j ⟩
               in  s- ₁ , t- ₁

  coerce-Σ′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (s : S ₁) (t : T ₁ s)
             → (s , t) [ ₁ ∣ ⟨ i ⟩ Σ (S i) (T i) ∣ ₀ ⟩ ↦
               let s- : (j : I) → S j
                   s- j = s [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
                   t- : (j : I) → T j (s- j)
                   t- j = t [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ j ⟩
               in  s- ₀ , t- ₀

  coerce-Π   : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : Π (S ₀) (T ₀))
             → (λ x → t x) [ ₀ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₁ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₁ ∣ ⟨ i ⟩ S i ∣ j ⟩
                   t- : (j : I) → T j (s- j)
                   t- j = t (s- ₀) [ ₀ ∣ ⟨ i ⟩ T i (s- i) ∣ j ⟩
               in  t- ₁

  coerce-Π′  : ∀ ℓ (S : I → Set ℓ) (T : (i : I) → S i → Set ℓ) (t : Π (S ₁) (T ₁))
             → (λ x → t x) [ ₁ ∣ ⟨ i ⟩ Π (S i) (T i) ∣ ₀ ⟩ ↦ λ x →
               let s- : (j : I) → S j
                   s- j = x [ ₀ ∣ ⟨ i ⟩ S i ∣ j ⟩
                   t- : (j : I) → T j (s- j)
                   t- j = t (s- ₁) [ ₁ ∣ ⟨ i ⟩ T i (s- i) ∣ j ⟩
               in  t- ₀

  coerce-─   : ∀ ℓ (S T : I → Set ℓ) (Q : S ₀ ─ T ₀)
             → Q [ ₀ ∣ ⟨ i ⟩ S i ─ T i ∣ ₁ ⟩ ↦
               (⟨ i ⟩ S (i [ ₁ - ₀ ])) ∘ Q ∘ (⟨ i ⟩ T i)


  coerce-─′  : ∀ ℓ (S T : I → Set ℓ) (Q : S ₁ ─ T ₁)
             → Q [ ₁ ∣ ⟨ i ⟩ S i ─ T i ∣ ₀ ⟩ ↦
               (⟨ i ⟩ S i) ∘ Q ∘ (⟨ i ⟩ T (i [ ₁ - ₀ ]))

{-# REWRITE coerce-∘  #-}
{-# REWRITE coerce-∘′ #-}
{-# REWRITE coerce-Σ  #-}
{-# REWRITE coerce-Σ′ #-}
{-# REWRITE coerce-Π  #-}
{-# REWRITE coerce-Π′ #-}
{-# REWRITE coerce-─  #-}
{-# REWRITE coerce-─′ #-}

refl : ∀ {ℓ} {A : Set ℓ} {a : A} → a ─ a
refl {a = a} = ⟨ _ ⟩ a

cong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B)
       {x y : A} → x ─ y → f x ─ f y
cong f p = ⟨ i ⟩ f (p $ i)

subst : ∀ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ')
        {x y : A} → x ─ y → B x → B y
subst B p b = b [ ₀ ∣ cong B p ∣ ₁ ⟩

funext : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {f g : (x : A) → B x}
           → (∀ x → f x ─ g x) → f ─ g
funext p = ⟨ i ⟩ (λ x → p x $ i)

module _ where
  open import Data.Nat

  _+1 : ℕ → ℕ
  x +1 = x + 1

  p : _+1 ─ suc
  p = funext lem
    where
      lem : ∀ x → (x + 1) ─ suc x
      lem zero = refl
      lem (suc x) = cong suc (lem x)

  test : 5 ─ 5
  test = cong (λ f → f 4) p

J : ∀ {ℓ ℓ′} {A : Set ℓ} {x : A} (P : (y : A) → x ─ y → Set ℓ′)
  → P x refl → {y : A} (e : x ─ y) → P y e
J P p e = p [ ₀ ∣ ⟨ i ⟩ P (e $ i) (⟨ j ⟩ (e $ (j [ ₀ - i ]))) ∣ ₁ ⟩

J-refl : ∀ {ℓ ℓ′} {A : Set ℓ} {x : A} (P : (y : A) → x ─ y → Set ℓ′)
       → (p : P x refl) → J P p refl ─ p
J-refl P p = refl

_-[_]-_ : ∀ {ℓ} {A B : Set ℓ} → A → A ─ B → B → Set ℓ
x -[ Q ]- y = x [ ₀ ∣ Q ∣ ₁ ⟩ ─ y
