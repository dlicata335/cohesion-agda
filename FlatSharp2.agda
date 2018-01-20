{-# OPTIONS --rewriting --without-K #-}

{-

To get Andrea Vezzosi's flat-ified Agda:

git clone https://github.com/agda/agda
cd agda
git checkout flat
cabal install --program-suffix=-flat

and then change your emacs startups to point to agda-flat and agda-mode-flat

-}

open import Agda.Primitive

module FlatSharp2 where

  -- library 

  data _==_ {l1 : Level} {A : Set l1} (a : A) : A → Set l1 where
    refl : a == a

  transport : ∀ {l1 l2 : Level} {A : Set l1} (C : A →  Set l2) {M N : A} (P : M == N) → C M → C N
  transport C refl x = x

  ap : ∀ {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A → B) → M == N → (f M) == (f N)
  ap f refl = refl

  apc : ∀ {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} {B : Set l2} {M N :{♭} A}
       (f : (x :{♭} A) → B) → M == N → (f M) == (f N)
  apc f refl = refl

  -- ap2 :  {A B C : Set} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  -- ap2 f refl refl = refl

  ! : {l1 : Level} {A : Set l1} {M N : A} → M == N → N == M
  ! refl = refl

  _∘_  : {l1 : Level} {A : Set l1} {M N P : A} → N == P → M == N → M == P
  β ∘ refl = β

  record Σe {l1 l2 : Level} (A : Set l1) (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σe public

  Σ : {l1 l2 : Level} {A : Set l1} -> (B : A -> Set l2) -> Set (l1 ⊔ l2)
  Σ {_}{_}{A} B = Σe A B

  infixr 0 _,_

  -- ----------------------------------------------------------------------

  data ♭ {l :{♭} Level} (A :{♭} Set l) : Set l where
    ♭i : (a :{♭} A) → ♭ A

  counit : ∀ {l :{♭} _} {A :{♭} Set l} → ♭ A → A
  counit (♭i x) = x

  ♭elim : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : ♭ A → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x : ♭ A) → C x
  ♭elim C f (♭i x) = f x

  -- crisp flat induction and crisp id induction are provable by pattern matching

  ♭elim-crisp : ∀ {c} {l :{♭} Level} {A :{♭} Set l}
         → (C : (x :{♭} ♭ A) → Set c)
         → ((u :{♭} A) → C (♭i u))
         → (x :{♭} ♭ A) → C x
  ♭elim-crisp C f (♭i x) = f x

  ff1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♭ A) → ♭ A
  ff1 (♭i (♭i x)) = ♭i x

  ff2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♭ A) 
  ff2 (♭i x) = ♭i (♭i x)

  ff3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → ff1 (ff2 x) == x
  ff3 (♭i x) = refl

  ff4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♭ A)) → ff2 (ff1 x) == x
  ff4 (♭i (♭i x)) = refl

  path-ind-crisp : ∀ {l :{♭} Level} {A :{♭} Set l} {a :{♭} A}
         → (C : (y :{♭} A) (p : a == y) → Set l)
         → C a refl
         → (y :{♭} A) (p :{♭} a == y) → C y p
  path-ind-crisp C b _ refl = b


  -- ----------------------------------------------------------------------
  -- sharp

  postulate
    Rewrite : {l1 : Level} {A : Set l1} → A → A → Set l1
  {-# BUILTIN REWRITE Rewrite #-}

  -- postulate ♯ is a monadic modality
  postulate
    ♯  : {l : Level} (A : Set l) → Set l
    ♯i : {l : Level} {A : Set l} → A → ♯ A
    ♯-elim : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) 
           → ((x : A) → ♯ (C (♯i x)))
           → ((x : ♯ A) → ♯ (C x))
    ♯-elim-β : {l1 l2 : Level} {A : Set l1} (C : ♯ A → Set l2) 
               → (f : (x : A) → ♯ (C (♯i x)))
               → (x : A) 
               → Rewrite (♯-elim C f (♯i x)) (f x)
    {-# REWRITE ♯-elim-β #-}

  -- postulate fusion iso 1:
  -- judgemental version of "induced map ♭ A → ♭ (♯ A) is an equivalence" 
  postulate
    ♭♯e : {l :{♭} Level} {A :{♭} Set l} → (x :{♭} (♯ A)) → A
    ♭♯β : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → Rewrite (♭♯e (♯i x)) x
    ♭♯η : {l :{♭} Level} {A :{♭} Set l} (x :{♭} ♯ A) → x == ♯i (♭♯e x)
  {-# REWRITE ♭♯β #-}
  postulate
    -- coherence between β (which is a rewrite so definitional) and η
    ♭♯η-triangle : {l :{♭} Level} {A :{♭} Set l} (x :{♭} A) → ♭♯η (♯i x) == refl

  -- internalized with types:

  fs1 : {l :{♭} Level} {A :{♭} Set l} → ♭ (♯ A) → ♭ A
  fs1 = ♭elim _ (\ u → ♭i (♭♯e u))

  fs2 : {l :{♭} Level} {A :{♭} Set l} → ♭ A → ♭ (♯ A) 
  fs2 (♭i x) = ♭i (♯i x)

  fs3 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ A) → fs1 (fs2 x) == x
  fs3 (♭i x) = refl

  fs4 : {l :{♭} Level} {A :{♭} Set l} (x : ♭ (♯ A)) → fs2 (fs1 x) == x
  fs4 (♭i x) = apc ♭i (! ( (♭♯η x) ))

  module PostulateIso where
    -- fusion iso 2:
    -- judgemental version of "induced map ♯ (♭ A) → # A is an equivalence" 
    
    ♯counit : {l :{♭} Level} {A :{♭} Set l} → ♯ (♭ A) → ♯ A
    ♯counit = ♯-elim _ (\x → ♯i (counit x)) 
  
    postulate
      ♯♭i : {l :{♭} Level} {A :{♭} Set l} → ♯ A → ♯ (♭ A)
      ♯♭β : {l :{♭} Level} {A :{♭} Set l} (x : ♯ A) → (♯counit (♯♭i x)) == x
      ♯♭η : {l :{♭} Level} {A :{♭} Set l} (x : ♯ (♭ A)) → (♯♭i (♯counit x)) == x
      -- TODO: coherence between β (which is a rewrite so definitional) and η

    -- universe of codiscrete types is codiscrete
    promote-nondep : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} 
                (C : Set l2) 
              → ((x :{♭} A) → ♯ C)
              → (x : A) → ♯ C
    promote-nondep C f x =  ♯-elim (\ _ → C) (♭elim _ f) (♯♭i (♯i x))  
  
    -- goes up a universe level
    escape : {l : Level} → ♯ (Set l) → Set (lsuc l)
    escape {l} A =  Σ (\ (x : ♯ (Σ \ (A : Set l) → A)) → p x == A)  where
      p : {l : Level} → ♯ (Σ \ (A : Set l) → A) → ♯ (Set l)
      p = ♯-elim _ (\ x → ♯i (fst x))

    escape-♯i-e : {l : Level} → (A : (Set l)) → escape (♯i A) → ♯ A
    escape-♯i-e = {!!}
    escape-♯i-i : {l : Level} → (A : (Set l)) → ♯ A → escape (♯i A) 
    escape-♯i-i = {!!}

    -- seems to need to use ♯Type to derive promote from the iso?

    promote : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} 
                (C : A → Set l2) 
              → ((x :{♭} A) → ♯ (C x))
              → (x : A) → ♯ (C x)
    promote {A = A} C f x = 
      foo (♯-elim (λ (x₁ : ♯ (♭ A)) → escape (♯-elim (\ _ → Set _) (\ x → ♯i (C (counit x))) x₁) )
                                     (♭elim _ (\ u → ♯-elim (\ _ → (escape (♯i (C u)))) (\ z → ♯i (escape-♯i-i _ (♯i z))) (f u))) 
                                     ((♯♭i (♯i x)))) 
      where foo : _ → _ 
            foo = {!!} -- ♯-elim (\ _ → (C x)) (\z → ♯i {!escape-♯i-e _ z!}) 
    
    promoteβ : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} (C : A → Set l2) 
              → (f : (x :{♭} A) → ♯ (C x))
              → (x :{♭} A) → (promote C f x) == (f x)
    promoteβ = {!!}

    

  module PostulatePromote where

    postulate
      promote : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} 
                  (C : A → Set l2) 
                → ((x :{♭} A) → ♯ (C x))
                → (x : A) → ♯ (C x)
        
      promoteβ : {l1 :{♭} Level} {l2 : Level} {A :{♭} Set l1} (C : A → Set l2) 
                → (f : (x :{♭} A) → ♯ (C x))
                → (x :{♭} A) → (promote C f x) == (f x)

    Code : {l : Level} {A : Set l} (x y : ♯ A) → Set l
    Code = ♯-elim _ (\ x → ♯-elim _ \ y → ♯i x == ♯i y) 


    -- internalized

    sf1 : {l :{♭} Level} {A :{♭} Set l} → ♯ (♭ A) → ♯ A
    sf1 = ♯-elim _ (\x → ♯i (counit x))
  
    sf2 : {l :{♭} Level} {A :{♭} Set l} → ♯ A → ♯ (♭ A) 
    sf2 = ♯-elim _ (promote _ (\ x → ♯i (♭i x)))
  
    sf3 : {l :{♭} Level} {A :{♭} Set l} → (x : ♯ A) → sf1 (sf2 x) == x
    sf3 {A = A} = {!!}  -- need ==_# is codiscrete, and codiscrete version of ♯ elim, but 
                        -- those hold for any modality
    {-
    ♯-elim _ (\ _ → Codisc-= (Codisc-♯)) (promote _ (\ _ → Codisc-= (Codisc-♯)) 
                  (\ x → (♯-elim-β (\ _ → ♯ A)(λ _ → Codisc-♯) (\x → ♯i (counit x)) (♭i x)  ∘ 
                           (ap (♯-elim (λ _ → ♯ A) (λ _ → Codisc-♯) (λ x₁ → ♯i (counit x₁))) 
                               (promoteβ (λ _ → ♯ (♭ A)) (λ _ → Codisc-♯) (λ x₁ → ♯i (♭i x₁)) x) 
                            ∘ ap sf1 (♯-elim-β _ (\ _ → Codisc-♯) (promote _ (\ _ → Codisc-♯) (\ x → ♯i (♭i x))) x)) 
                           )) )
    -}
  
    sf4 : {l :{♭} Level} {A :{♭} Set l} → (x : ♯ (♭ A)) → sf2 (sf1 x) == x
    sf4 = {!!} -- ♯-elim _ (\ _ → Codisc-= (Codisc-♯)) (promote _ (\ _ → Codisc-= (Codisc-♯)) (♭elim-crisp _ {!similar!}) )
  

    Codiscs : {l : Level} → Set (lsuc l)
    Codiscs {l} = Σ \ (A : Set l) → A == ♯ A

    -- but promote doesn't seem to give that the universe of codiscrete types is codiscrete

    from-Codiscs : {l : Level} → ♯ (Codiscs{l}) → Codiscs{l}
    from-Codiscs A = {!!}

{-

  Σ-interact-crisp1 : {A :{♭} Set} {B :{♭} A → Set} → ♯(Σ B) → 
               Σ \ (x : ♯ A) → fst (promote (\ _ → Codiscs) (\ _ → Codisc-Codisc) (\ x → (♯ (B (♯e x))) , Codisc-♯) x)
  Σ-interact-crisp1 {A = A} {B = B} p = 
     ♯-rec Codisc-♯ (\ p' → ♯i (fst p')) p , 
     promote 
     (\ q → fst (promote (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) 
     (\ q → snd (promote (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) 
     (\ q → transport fst (! (promoteβ (λ _ → Codiscs) (λ _ → Codisc-Codisc) (λ x → ♯ (B (♯e x)) , Codisc-♯) (♯-rec Codisc-♯ (\ p' → ♯i (fst p')) q))) (transport (\ h → ♯ (B h)) (apc ♯e (! (♯-rec-crisp-β Codisc-♯ (λ p' → ♯i (fst p')) q)) ) (♯i (snd (♯e q))))) p

  escape : ♯ Set → Set
  escape A = fst (promote (\ _ → Codiscs) (λ _ → Codisc-Codisc) (\ X → ♯ (♯e X) , Codisc-♯) A)

  escape-♯i-crisp : (A :{♭} Set) → escape (♯i A) == ♯ A
  escape-♯i-crisp X = ap fst (promoteβ (λ _ → Σe Set Codisc) (λ _ → Codisc-Codisc) (λ X₁ → ♯ (♯e X₁) , Codisc-♯) (♯i X))
  
  escape-♯i-1 : (A : Set) → escape (♯i A) → ♯ A
  escape-♯i-1 A = 
    promote (\ X → escape (♯i X) -> ♯ X) (\ _ → Codisc-Π (\ _ → Codisc-♯)) 
            (\ X → transport (\ X → X) (escape-♯i-crisp X))
            A 

  escape-♯i-2 : (A : Set) → ♯ A → escape (♯i A) 
  escape-♯i-2 A = 
    promote (\ X → ♯ X -> escape (♯i X)) 
            (\ _ → Codisc-Π (\ _ → snd (promote (\ _ → Codiscs) (λ _ → Codisc-Codisc) (\ X → ♯ (♯e X) , Codisc-♯) _))) 
            (\ X → transport (\ X → X) (! (escape-♯i-crisp X)))
            A 
-}
