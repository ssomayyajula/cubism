\documentclass[11pt,letterpaper]{article}

% Language
\usepackage[english]{babel}

% Set margins
\usepackage[margin=1in]{geometry}
\usepackage{float}

% Math
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}

\usepackage{verbatim}

% Links
\usepackage{hyperref}

\usepackage{tikz}

% Enable Literate Agda
\usepackage[references,links]{agda}

% Set Sans font for Agda code
\setsansfont[Scale=MatchLowercase]{DejaVuSansMono.ttf}

% Environments & Commands
\newcommand{\D}{\AgdaDatatype}
\newcommand{\F}{\AgdaFunction}
\newcommand{\Arg}{\AgdaArgument}
\newcommand{\Con}{\AgdaInductiveConstructor}

\newcommand{\removelinebreaks}[1]{
  \begingroup\def\\{ }#1\endgroup}

\newtheorem{theorem}{Theorem}[section]

\theoremstyle{definition}
\newtheorem{definition}{Definition}

\newcommand{\Path}{\D{Path}}
\newcommand{\comp}{\F{comp}}

\newcommand{\drawpath}[4]{
  \node at (0,0) (#2) {\Arg{#2}};
  \node at (#4,0) (#3) {\Arg{#3}};
  \draw[->] (#2) -- node[above] {\Arg{#1}} (#3);
}

\title{Excursions in Cubical Type Theory}
\author{Siva Somayyajula}

\begin{document}
\maketitle

\tableofcontents

\section{Motivation}

In recent years, the \emph{univalent foundations} program has aimed to develop a foundations of constructive mathematics with an enriched notion of equality. Technicality aside, recall that your average intensional type theory may only express intensional equalities between mathematical objects. Unlike extensional type theories, they may not express, for example, the extensional equality of functions. However, an intensional type theory with the \emph{univalence axiom} may identify equivalent types as equal for an appropriate definition of equivalence. Consequently, function extensionality becomes a theorem in this system, and many results that require a coarser notion of equality become provable. As Jon Sterling said in an episode of the Type Theory Podcast, ``in a sense, [this] is more extensional than extensional type theory,'' because the range of expressible equalities based on the behavior of objects is widened. In fact, univalence is expressly \emph{inconsistent} with extensional type theory, so it seems that an intensional and univalent type theory poses many benefits over existing systems.

\emph{Homotopy type theory} (HoTT), the first such type theory developed by this program, extends Martin-L\"of type theory with the univalence axiom and other constructs to develop synthetic proofs of results in homotopy theory. Indeed, given our above exposition, HoTT seems to be the type theory to end all type theories. However, its critical weakness is that univalence lacks a computation rule. This is not an issue for those who intend to leverage HoTT for proofs, but what of programmers and constructivists? There are many situations where one may want to use univalence to seamlessly switch between different views of the same abstract type when writing a software application, or actually run one's proofs. While these programs and proofs would enjoy various type safety guarantees in HoTT, they would also just get \emph{stuck}. Enter \emph{cubical type theory} (CuTT), which is advertised as providing a ``constructive interpretation of the univalence axiom;'' that is, univalence gets a computation rule. We will give a brief introduction to CuTT and demonstrate its power and computational benefits in a variety of case studies motivated by concerns in mathematics and software engineering, all in Agda. Note that proofs pulled form external sources are cited either in the source code or in this paper; and, unless specified, definitions are taken from \cite{hottbook}.
\section{Cubical Type Theory}

CuTT starts with intuitionistic type theory and then introduces a set of primitive types that ultimately capture the topological notion of an $n$-dimensional cube. We will begin with the type of \emph{intervals}.

\subsection{Intervals and Paths}

Consider the unit interval $I=[0,1]$ and some basic facts about it. In particular, $I$ is bounded by least and greatest elements $0$ and $1$, respectively. We also have trivial equalities $1-0=1$ and $1-1=0$. Perhaps more interestingly, for all $r,s\in I$:

\begin{align*}
1-\max(r,s)&=\min(1-r,1-s)\\
1-\min(r,s)&=\max(1-r,1-s)
\end{align*}

Together, these properties make $(I, \max, \min, 0, 1)$ a bounded distributive lattice and $r\mapsto 1-r$ a De Morgan involution. In other words, $(I, \max, \min, 0, 1, r\mapsto 1-r)$ is a De Morgan algebra. Thus, it is appropriate to refer to $\max$ as $\lor$, $\min$ as $\land$, and $r\mapsto 1-r$ as $\sim$.

\AgdaHide{
\begin{code}
{-# OPTIONS --cubical --rewriting #-}

module _ where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Function using (id; _$_; _∘_; flip)
open import Data.Product hiding (map)

module Primitives where
  open import Agda.Primitive.Cubical public renaming
    (primINeg   to  ~_;
     primIMax   to _∨_;
     primIMin   to _∧_;
     primComp   to comp;
     isOneEmpty to empty)

-- Saizan's plumbing
module Unsafe' (dummy : Set₁) = Primitives
unsafeComp = Unsafe'.comp Set
unsafePOr = Unsafe'.primPOr Set

open Primitives public

\end{code}}

Now, fix a countable set of names $N$. We obtain a \emph{homotopical} (that is, considering only the boundary elements) notion of $I$ via the \emph{set} \D{I} defined by the following grammar and quotiented by the aforementioned properties. Note that the inclusion of only $\Con{i0}$ and $\Con{i1}$ does not allow us to prove $(\F{\sim}~\Arg{r})~\F{\land}~\Arg{r}=\Con{i0}$ or $(1-\Arg{r})\lor\Arg{r}=\Con{i1}$---\D{I} is faithful to the original definition of $I$.

$$r,s:=\Con{i0}\,\mid\,\Con{i1}\,\mid\,i\in N\,\mid\,\F{\sim}\Arg{r}\,\mid\,\Arg{r}~\F{\land}~\Arg{s}\,\mid\,\Arg{r}~\F{\lor}~\Arg{s}$$

Note that CuTT defines \D{I} as a set, as opposed to a type, for technical reasons \cite{mortberg_2017}. Now, consider that topological paths over a space $A$ are defined as continuous functions from the $I$ to $A$. We may recover a similar definition in CuTT via the \emph{type} \Path. However, we cannot define $\Path:=\D{I}\to\D{A}$ directly since \D{I} is not a type. Once again though, we are only concerned with the ``boundary behavior'' of a topological path $f$---the elements $f(0)$ and $f(1)$. As a result, we define a type $\Path~\Arg{t}~\Arg{u}$ to be the type of paths between endpoints $\Arg{t},\Arg{u}:\D{A}$. As a result, one may introduce a \emph{path abstraction} $\lambda~i\to e:\Path~e[\Con{i0}/i]~e[\Con{i1}/i]$ where $i\in N$. Path abstractions and applications have the expected judgmental equalities with respect to lambda abstractions and applications, except our attention is restricted to \D{I} \cite{cutt16}.

\AgdaHide{
\begin{code}
postulate
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ

{-# BUILTIN PATHP PathP #-}

Path : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
Path {A = A} = PathP (λ _ → A)
\end{code}}

Perhaps that after dealing with this level of abstraction (pun intended), we deserve a few examples where we reason about the basic properties of paths.

\AgdaNoSpaceAroundCode{
\begin{theorem}[Constant/identity path]
If $\Arg{x}:A$, we have
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x : A} where
\end{code}}
\begin{code}
  idp : Path x x
\end{code}
\end{theorem}
\begin{proof}
We want a path abstraction that is invariant on an element in \D{I}, so
\begin{code}
  idp _ = x
\end{code}
\end{proof}

\begin{theorem}[Path inversion]
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y : A} where
  infix 120 _⁻¹
\end{code}}
\begin{code}
  _⁻¹ : Path x y → Path y x
\end{code}
\end{theorem}
\begin{proof}
Given a path $\Arg{p}$ from $\Arg{x}$ to $\Arg{y}$, $\Arg{p}~(\F{\sim}~\Con{i0})=\Arg{p}~\Con{i1}=\Arg{y}$ and $\Arg{p}~(\F{\sim}~\Con{i1})=\Arg{p}~\Con{i0}=\Arg{x}$, so:
\begin{code}
  p ⁻¹ = λ i → p (~ i)
\end{code}
\end{proof}

\begin{theorem}[Action on paths]
If $\Arg{f}:\D{A}\to\D{B}$ and $\Arg{x},\Arg{y}:\D{A}$, we have
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x y : A} where
\end{code}}
\begin{center}
\begin{code}
  ap : Path x y → Path (f x) (f y)
\end{code}
\end{center}
\end{theorem}
\begin{proof}
Given a path \Arg{p} from \Arg{x} to \Arg{y}, $\Arg{f}~(\Arg{p}~\Con{i0})=\Arg{f}~\Arg{x}$ and $\Arg{f}~(\Arg{p}~\Con{i1})=\Arg{f}~\Arg{y}$, so:
\begin{code}
  ap p i = f (p i)
\end{code}
\end{proof}
}

Paths look suspiciously like the identity type---in particular, these examples correspond to reflexivity, symmetry, and function substitutivity, respectively. Indeed, we will see how we may leverage paths to represent equalities; but first, we will see why CuTT is cubical. If $P_n$ is a type family parameterized by $n$ intervals, it induces the an $n$-dimensional cube; see the top of page 6 in \cite{cutt16}. The manipulation of paths will allow us to do mathematics and programming.

\subsection{Modeling Equality}

We claim that we can model equality \'a la Leibniz using paths, so let's introduce a convenient alias.

\begin{code}
_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ = Path
\end{code}

First, we will see how paths help us model extensional equality.

\begin{definition}[Homotopy]
The space of \emph{homotopies} between two functions is defined as follows.
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
\end{code}}
\begin{code}
  _∼_ : (f g : (x : A) → P x) → Set _
  f ∼ g = ∀ x → f x ≡ g x
\end{code}
\end{definition}

Though topologically inspired, it is useful to think of the inhabitants of this type as proofs that two such functions are extensionally equal. As a result, we can prove the obvious: equal functions are \emph{homotopic}.

\AgdaHide{
\begin{code}
  module _ {f g : (x : A) → P x} where
\end{code}}

\begin{theorem}
\begin{code}
    app≡ : f ≡ g → f ∼ g
\end{code}
\end{theorem}
\begin{proof}
Given $p:f\equiv g$, we can produce a path $f~x≡g~x$ by the term $\lambda~i\to p~i~x$. One can validate this result by doing the same case analysis on $i$ as in the previous proofs.
\begin{code}
    app≡ p x i = p i x
\end{code}
\end{proof}

And, as desired, we can prove function extensionality.

\begin{theorem}[Function extensionality]
\begin{code}
    λ≡ : f ∼ g → f ≡ g
\end{code}
\end{theorem}
\begin{proof}
This proof is subtle---we need to construct a path abstraction that returns $f$ on \Con{i0} and $g$ on \Con{i1}. Given the homotopy $h$, $h~x$ will give $f~x\equiv g~x$, so applying $i$ will give $f~x$ at \Con{i0} and $g~x$ at \Con{i1}. By $\eta$-conversion, we have given $f$ at \Con{i0} and $g$ at \Con{i1}, as desired.
\begin{code}
    λ≡ h i x = h x i
\end{code}
\end{proof}

Furthermore, it is easy to see that \F{app≡} and \F{λ≡} are definitional inverses. It follows that the space of homotopies is equivalent to the space of paths on functions. Now, back to our regularly scheduled programming. Recall what is necessary for an equality to be Leibnizian \cite{leibnizeq}; it must satisfy:

\begin{enumerate}
\item Reflexivity
\item Function substitutivity
\item Indiscernibility of identicals
\end{enumerate}

We have already shown (1) and (2), so it remains to show (3). First, we must define \emph{type coercion}: given that $\Arg{A}\equiv\Arg{B}$, we can convert $\Arg{x}:\Arg{A}$ to a term of type \Arg{B}. It is not immediately clear that such an operation exists given the current machinery we have for paths. However, CuTT comes with a path composition primitive \F{comp} that ``completes'' a partially specified cube.

\begin{theorem}[Type coercion]
\AgdaHide{
\begin{code}
module _ {ℓ} {A B : Set ℓ} where
\end{code}}
\begin{code}
  coe : A ≡ B → A → B
\end{code}
\end{theorem}
\begin{proof}
We realize a 0-dimensional or \F{empty} cube (that is, a single point) by partially specifying it at $p~\Con{i0}=A$ with the given $x:A$. Thus, we get an element of type $p~\Con{i1}=B$.
\begin{code}
  coe p x = comp (λ i → p i) _ (λ _ → empty) x
\end{code}
\end{proof}

Furthermore, we can prove that coercion on the constant path has no computational effect, as desired. This is also a \emph{propositional computation rule} because it dictates, up to propositional equality represented by paths, how \F{coe} behaves on certain inputs.

\begin{theorem}[Degenerate coercion]
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} where
\end{code}}
\begin{code}
  coe-β : (x : A) → coe idp x ≡ x
\end{code}
\end{theorem}
\begin{proof}
Consider the square in figure \ref{fig:coebeta} we would like to complete where \tikz[baseline]{\drawpath{p~i}{x}{y}{1}} denotes $\Arg{p}:\Path~\Arg{x}~\Arg{y}$ applied to an element \Arg{i} of \D{I}.
\begin{figure}[H]
\centering
\begin{tikzpicture}[->]
  \node at (0,0) (x1) {x};
  \node at (0,3) (x2) {\F{coe}~\F{idp}~\Arg{x}};
  \node at (3,0) (x3)  {\Arg{x}};
  \node at (3,3) (x4)  {\Arg{x}};

  \path
    (x1) edge[dashed] node[left]  {?}         (x2)
    (x2) edge[dashed] node[above] {?}         (x4)
    (x1) edge         node[below] {$\F{idp}~i$} (x3)
    (x3) edge         node[right] {$\F{idp}~j$} (x4);
\end{tikzpicture}
\label{fig:coebeta}
\end{figure}
Composition will complete the dashed sides as long as we specify the bottom face and the right side (where $i=\Con{i1}$).
\begin{code}
  coe-β x i = comp (λ _ → A) _ (λ { j (i = i1) → x }) x
\end{code}
\end{proof}

The indiscernibility of identicals follows immediately by coercion and action of paths.

\begin{theorem}[Indiscernibility of identicals]
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} where
\end{code}}
\begin{code}
  transport : (P : A → Set ℓ₂) {x y : A} → x ≡ y → P x → P y
  transport⁻¹ : (P : A → Set ℓ₂) {x y : A} → x ≡ y → P y → P x
\end{code}
\end{theorem}
Consider $P$ to be a type-level function; then, the proof is trivial.
\begin{proof}

\begin{code}
  transport   P = coe ∘ ap P
  transport⁻¹ P = transport P ∘ _⁻¹
\end{code}
\end{proof}

Now that we've proven to ourselves that paths are indeed a faithful representation of equality, we will develop a powerful inductive principle to reason about them---Paulin-Mohring's \F{J}, or \emph{path induction}. But first, some definitions.

\begin{definition}[Contractible space]
We say a space is \emph{contractible} if and only if it is equivalent to a single point.
\begin{code}
isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = ∃ λ x → ∀ (y : A) → x ≡ y
\end{code}
We say that we can \emph{contract} \Arg{A} to \Arg{x}.
\end{definition}

\begin{definition}[Singleton space \cite{cutt16}]
The \emph{singleton space} is the space of paths fixed at a base point.
\begin{code}
singl : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
singl a = ∃ λ x → Path a x
\end{code}
\end{definition}

We can immediately prove that the singleton space is contractible.

\begin{theorem}
\AgdaHide{
\begin{code}
-- <j> p (i ∧ j) : Path x (p i) b/c @ i0 = p i0 = x and @ i1 = p i
module _ {ℓ} {A : Set ℓ} {x : A} where
\end{code}}
\begin{code}
  singlIsContr : isContr (singl x)
\end{code}
\end{theorem}
\begin{proof}
We claim that we can contract this type to $(\Arg{x}, \F{idp})$ i.e. that for any $(y,p)$, $(x,idp)\equiv(y,p)$. Thus, we construct a path abstraction valued $(x,p)$ at \Con{i0} and $(y,p)$ at \Con{i1}. Clearly, $p$ takes care of the first component, but now we have to show $x\equiv p~i$ for the second component. We claim that $\lambda j\to p~(i\land j)$ works by case analysis on $j$---at \Con{i0}, we have $p~(i\land\Con{i0})=p~\Con{i0}=x$ and at \Con{i1}, we have $p~(i\land\Con{i1})=p~i$, as desired.
\begin{code}
  singlIsContr = (x , idp) , λ { (_ , p) i → p i , λ j → p (i ∧ j) }
\end{code}
\end{proof}

This is a (known) remarkable result, with the CuTT proofs from \cite{cutt16}---under the right conditions, any path can be contracted to the constant path. Topologically, this makes sense---the singleton space consists of all paths fixed at a basepoint $a$, but free at another. So, we can ``unhook'' the path at the free endpoint and pull it back to $a$. As a result, this contraction is only possible if at least one endpoint is freely quantified. We can rephrase this contractibility result in terms of an induction principle. Paulin-Mohring's $J$, or \emph{path induction} in homotopy type theory, is the principle that to prove any proposition over a path with at least one free endpoint, it suffices to prove the case for the constant path.

\begin{theorem}[Paulin-Mohring's $J$]
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {x : A} where
\end{code}}
\begin{code}
  J : (P : ∀ y → Path x y → Set ℓ₂) (r : P x idp) {y : A} (p : Path x y) → P y p
\end{code}
\end{theorem}
\begin{proof}
We transport the case for the constant path along the contractibility result to yield the proof for any path.
\begin{code}
  J P r {y} p = transport (uncurry P) (proj₂ singlIsContr (y , p)) r
\end{code}
\end{proof}

We can go even further and prove a propositional computation rule for \F{J}; as expected, when applied to \F{idp}, it returns the provided case for \F{idp}. Unfortunately, this rule only holds up to paths, but the original CuTT paper defines Martin-L\"of's \emph{identity type} in terms of paths in a way where this rule holds definitionally \cite{cutt16}.

\begin{theorem}
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {x : A} {P : ∀ y → Path x y → Set ℓ₂} {r : P x idp} where
\end{code}}
\begin{code}
  J-β : J P r idp ≡ r
\end{code}
\end{theorem}
Since \F{J} is defined in terms of \F{transport}, which is itself defined in terms of \F{coe}, this result is a corollary of its propositional computation rule.
\begin{proof}
\begin{code}
  J-β = coe-β r
\end{code}
\end{proof}

Path induction is quite powerful because we can reduce many proofs involving paths to the simpler constant path case. In fact, we may easily define path composition, or transitivity of equality, using this principle.

\begin{theorem}[Composition of paths]
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y z : A} where
  infixr 80 _∙_
\end{code}}
\begin{code}
  _∙_ : Path x y → Path y z → Path x z
\end{code}
\end{theorem}
\begin{proof}
Originally, we are asked to give the following unknown path.
\begin{figure}[H]
\centering
\begin{tikzpicture}[->]
  \node at (0,0) (x)  {\Arg{x}};
  \node at (3,0) (y)  {\Arg{y}};
  \node at (6,0) (z)  {\Arg{z}};

  \path
    (x) edge node[below] {\Arg{p}} (y)
    (y) edge node[below] {\Arg{q}} (z)
    (x) edge[dashed,bend left] node[above] {?} (z);
\end{tikzpicture}
\end{figure}
Using \D{J}, we can contract $p$, yielding the following.
\begin{figure}[H]
\centering
\begin{tikzpicture}[->]
  \node at (0,0) (x)  {\Arg{x},\Arg{y}};
  \node at (3,0) (z)  {\Arg{z}};

  \path
    (x) edge node[below] {\Arg{q}} (z)
    (x) edge[dashed,bend left] node[above] {?} (z);
\end{tikzpicture}
\end{figure}
Now, we can just return $q$!
\begin{code}
  _∙_ = J (λ y _ → Path y z → Path x z) id
\end{code}
\end{proof}

\begin{theorem}
Paths form an equivalence relation.
\end{theorem}
\AgdaHide{
\begin{code}
open import Relation.Binary using (IsEquivalence; Setoid)

PathIsEquivalence : ∀ {ℓ} {A : Set ℓ} → IsEquivalence (Path {A = A})
PathIsEquivalence = record
  { refl = idp
  ; sym = _⁻¹
  ; trans = _∙_ }

PathSetoid : ∀ {ℓ} → Set ℓ → Setoid ℓ ℓ
PathSetoid A = record
  { Carrier = A
  ; _≈_ = Path
  ; isEquivalence = PathIsEquivalence
  }

module _ {ℓ} {A : Set ℓ} where
  open import Relation.Binary.EqReasoning (PathSetoid A) public
\end{code}}

\subsection{Equivalences}
To prove (part of) univalence, the principle that equivalent types are equal, we need a type-theoretic notion of equivalence. One such definition is that $A\simeq B$ if and only if we have a function $f:A\simeq B$ such that for all $y:B$, there is a unique $x:A$ such that $y\equiv f~x$, obeying a notion of bijectivity. However, univalence is the even stronger claim that the space of equivalences between two types is equivalent to the respective space of paths. As a result, given a proof $e$ that $f$ is an equivalence and if we have $\F{equivToPath}$ and $\F{pathToEquiv}$, then $\F{pathToEquiv}~(\F{equivToPath}~(f,e))\equiv(f,e)$. It follows that these procedures do not change $f$, and most importantly, $e$. This is impossible to guarantee as-is---even though we would still have proof that $f$ is an equivalence, the original proof $e$ might get lost in transit. Thus, we must require a proof-irrelevant notion of equivalence such that any modifications to $e$ are indistinguishable in this proof system. We introduce the following definition of equivalence to get around this issue \cite{cutt16}.

\begin{definition}[Fiber space]
We co-opt this definition directly from set theory---the fiber of $y$ under $f$ is the inverse image of $\{y\}$ under $f$.
\AgdaHide{
\begin{code}
module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} where
\end{code}}
\begin{code}
  fiber : (f : A → B) (y : B) → Set _
  fiber f y = Σ[ x ∈ A ] y ≡ f x
\end{code}
\end{definition}

Now, we say that $f$ is an equivalence not only if it obeys the condition we gave above, but also if the proof that $y\equiv f~x$ is indistinguishable from any other such proof. That is, the fiber of every $y$ under $f$ is contractible.

\begin{definition}[Equivalence]
\AgdaHide{
\begin{code}
module _ {ℓ₁ ℓ₂} where
\end{code}}
\begin{code}
  isEquiv : (A : Set ℓ₁) (B : Set ℓ₂) → (A → B) → Set _
  isEquiv _ _ f = ∀ y → isContr (fiber f y)
\end{code}
\end{definition}

\AgdaHide{
\begin{code}
{-# BUILTIN ISEQUIV isEquiv #-}
\end{code}}

For convenience, we introduce the following alias that pairs $f$ with proof that it is an equivalence.

\begin{code}
infix 4 _≃_
_≃_ : ∀ {ℓ₁} {ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
A ≃ B = Σ (A → B) (isEquiv A B)
\end{code}

\AgdaHide{
\begin{code}
-- Saizan's plumbing for glues
module _ {ℓ} {A : Set ℓ} where
  contr : isContr A → (φ : I) → (u : Partial A φ) → A
  contr (c , p) φ u = comp (λ _ → A) φ (λ i o → p (u o) i) c

module _ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) where
  module _ (f : A ≃ B) (φ : I) (t : Partial A φ) (a : B {- [ φ ↦ f t ] -})
           (p : PartialP φ (λ o → a ≡ proj₁ f (t o))) where
    equiv : fiber (proj₁ f) a -- [ φ ↦ (t , λ j → a) ]
    equiv = contr (proj₂ f a) φ (λ o → t o , (λ i → p o i))
\end{code}}

Trivially, the identity function is an equivalence.

\begin{definition}[Identity equivalence]
\begin{code}
ide : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ide = id , λ y → singlIsContr {x = y}
\end{code}
\end{definition}

While this definition of equivalences certainly gets around the proof relevance problem, it is inconvenient to work with. In fact, it is more intuitive to think of equivalences as isomorphisms, like in the following definition.

\begin{definition}
A \emph{quasi-inverse} of $f$ is a function $g$ with proofs that $g$ is both a left and right inverse of $f$, up to homotopy.
\begin{code}
record qinv {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mkqinv
  field
    g : B → A
    ε : (g ∘ f) ∼ id
    η : (f ∘ g) ∼ id
\end{code}
This also corresponds to \emph{homotopy equivalence} in homotopy theory.
\end{definition}

We once again give a convenient alias for quasi-inverses.

\begin{code}
_≂_ : ∀ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → Set _
A ≂ B = Σ (A → B) qinv
\end{code}

Since quasi-inverses are not proof irrelevant, we cannot use them directly, but we may convert them to equivalences by the following theorem. The not-so-intuitive part of this proof is that we can develop proof irrelevant data from a quasi-inverse---you can see the proof of the \emph{grad lemma} \href{https://github.com/Saizan/cubical-demo/blob/master/src/Cubical/GradLemma.agda}{here} by Andrea Vezzosi (Saizan). 

\AgdaHide{
\begin{code}
-- By Saizan
Square : ∀ {ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
          (u : a0 ≡ a1) (v : b0 ≡ b1) (r0 : a0 ≡ b0) (r1 : a1 ≡ b1) → Set ℓ
Square u v r0 r1 = PathP (λ i → u i ≡ v i) r0 r1
\end{code}}

\begin{theorem}
\begin{code}
qinvToEquiv : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A ≂ B → A ≃ B
\end{code}
\end{theorem}
\begin{proof}
\begin{code}
qinvToEquiv {A = A} {B} (f , mkqinv g ε η) = f , λ y → (g y , η y ⁻¹) ,
  λ { (z , p) i → gy≡z p i , square p i } where
\end{code}
\AgdaHide{
\begin{code}
  -- A slightly unsuccessful reduction of Saizan's grad lemma
  gy≡z : ∀ {y z} → y ≡ f z → g y ≡ z
  gy≡z {z = z} p = ap g p ∙ ε z
  
  module _ {y z} (p : y ≡ f z) where
    postulate
      fill0 : Square (ap g (η y ⁻¹)) idp (idp {x = g y}) (ε (g y))
    {-fill0 i j = comp (λ _ → A) _ (λ k →
      λ { (i = i0) → g y
        ; (i = i1) → ε (g y) (j ∧ k)
        ; (j = i0) → g ((η y ⁻¹) i) }) (g ((η y ⁻¹) i))-}
    
      fill1 : Square (ap g p) (gy≡z p) idp (ε z)
    {-fill1 i j = comp (λ _ → A) _ (λ k →
      λ { (i = i1) → ε z (j ∧ k)
        ; (i = i0) → g y
        ; (j = i0) → g (p i) }) (g (p i))-}
    
    subsq : Square idp (ap (g ∘ f) (gy≡z p)) (ap g (η y ⁻¹)) (ap g p)
    subsq i j = comp (λ _ → A) _ (λ k →
      λ { (i = i0) → fill0 j (~ k)
        ; (i = i1) → fill1 j (~ k)
        ; (j = i0) → g y
        ; (j = i1) → ε (gy≡z p i) (~ k) }) (gy≡z p (i ∧ j))

    square : Square idp (ap f (gy≡z p)) (η y ⁻¹) p
    square i j = comp (λ _ → B) _ (λ k →
      λ { (i = i0) → η ((η y ⁻¹) j) k
        ; (i = i1) → η (p j) k
        ; (j = i0) → η y k
        ; (j = i1) → η (f (gy≡z p i)) k }) (f (subsq i j))
\end{code}}
\end{proof}

\subsection{Univalence, Almost}

Now that we have a sufficient theory of equivalences, we would like to formalize part of \emph{univalence} (the full proof can be found \href{https://github.com/Saizan/cubical-demo/blob/master/src/Cubical/Univalence.agda}{here}).

\begin{theorem}
For all types $A$ and $B$, $(A\equiv B)\simeq(A\simeq B)$. That is, the space of equivalences is equivalent to the space of paths.
\end{theorem}
\begin{proof}
We will give a function \F{pathToEquiv} and its quasi-inverse \F{ua} without the homotopy data. The former converts paths to equivalences by contracting them to the constant path and returning the identity equivalence.

\AgdaHide{
\begin{code}
module _ {ℓ} {A B : Set ℓ} where
\end{code}}
\begin{code}
  pathToEquiv : A ≡ B → A ≃ B
  pathToEquiv = J (λ B _ → A ≃ B) ide
\end{code}

\AgdaHide{
\begin{code}
-- Saizan's implementation of Kan filling (check original paper for reference implementation)
fill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
fill A φ u a0 i = unsafeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
  (λ j → unsafePOr φ (~ i) (u (i ∧ j)) λ { (i = i0) → a0 }) a0

--Saizan's plumbing for glue types
module _ {ℓ ℓ' : I → Level} {T : ∀ i → Set (ℓ i)} {A : ∀ i → Set (ℓ' i)}
         (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
         (t0 : T i0 {- [ φ ↦ t i0 ] -}) where
  private
    c1 c2 : A i1
    c1 = unsafeComp A φ (λ i → (λ { (φ = i1) → f i (t i itIsOne)})) (f i0 t0)
    c2 = f i1 (unsafeComp T φ t t0)

    a0 = f i0 t0

    a : ∀ i → Partial (A i) φ
    a i = (λ { (φ = i1) → f i ((t i) itIsOne)})

    u : ∀ i → A i
    u = fill A φ a a0

    v : ∀ i → T i
    v = fill T φ t t0

  pres : c1 ≡ c2
  pres j = unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ (j ∨ ~ j)
    (a i) \ { (j = i1) → f i (v i); (j = i0) → u i}) a0

module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) (φ : I)
      → (T : Partial (Set ℓ') φ) → (f : PartialP φ (λ o → T o → A))
      → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → PartialP φ T → A → primGlue A φ T f pf
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → primGlue A φ T f pf → A

open GluePrims public renaming (prim^glue to glue ; prim^unglue to unglue)

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) → (φ : I) → (T : Partial (Set ℓ') φ)
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ'
Glue A φ T f = primGlue A φ T (λ o → proj₁ (f o)) (λ o → proj₂ (f o))

module Unsafe'' (dummy : Set1) = GluePrims
module Unsafe''' = Unsafe'' Set

unsafeGlue = Unsafe'''.prim^glue

primitive
  primFaceForall : (I → I) → I

module FaceForall (φ : I → I) where
  δ = primFaceForall φ
  postulate
    ∀v : ∀ i → IsOne (φ i) → IsOne ((δ ∨ (φ i0 ∧ ~ i)) ∨ (φ i1 ∧ i))
    ∀e : IsOne δ → ∀ i → IsOne (φ i)

module _ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial (Set ℓ') φ}
           {f : (PartialP φ λ o → T o ≃ A)} where
  fwdGlueIso : PartialP φ (λ o → Glue A φ T f → T o)
  fwdGlueIso (φ = i1) = id

  backGlueIso : PartialP φ (λ o → T o → Glue A φ T f)
  backGlueIso (φ = i1) = id

  lemGlueIso : (b : PartialP φ (λ _ → Glue A φ T f)) → PartialP φ λ o →
                 (unglue {φ = φ} (b o)) ≡ (proj₁ (f o) (fwdGlueIso o (b o)))
  lemGlueIso _ (φ = i1) = idp

module CompGlue {ℓ ℓ' : I → Level} (A : ∀ i → Set (ℓ i))
                (φ : I → I) (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
                (f : ∀ i → PartialP (φ i) λ o → T i o ≃ A i)
                where
  B : ∀ i → Set (ℓ' i)
  B = λ i → Glue (A i) (φ i) (T i) (f i)

  module Local (ψ : I) (b : ∀ i → Partial (B i) ψ)
               (b0 : B i0 {- [ ψ ↦ b i0 ] -}) where
    a : ∀ i → Partial (A i) ψ
    a i = λ o → unglue {φ = φ i} (b i o)

    module Forall (δ : I) (∀e : IsOne δ → ∀ i → IsOne (φ i)) where
      a0 : A i0
      a0 = unglue {φ = φ i0} b0

      a1' = unsafeComp A ψ a a0

      t1' : PartialP δ (λ o → T i1 (∀e o i1))
      t1' o = unsafeComp (λ i → T i (∀e o i)) ψ
                (λ i o' → fwdGlueIso {φ = φ i} (∀e o i) (b i o'))
                (fwdGlueIso {φ = φ i0} (∀e o i0) b0)

      ω : PartialP δ _
      ω o = pres (λ i → proj₁ (f i (∀e o i))) ψ
              (λ i x → fwdGlueIso {φ = φ i} (∀e o i) (b i x))
              (fwdGlueIso {φ = φ i0} (∀e o i0) b0)

      a1'' = unsafeComp (λ _ → A i1) (δ ∨ ψ)
              (λ j → unsafePOr δ ψ (λ o → ω o j) (a i1)) a1'

      g : PartialP (φ i1) _
      g o = (equiv (T i1 _) (A i1) (f i1 o) (δ ∨ ψ)
        (unsafePOr δ ψ t1' (λ o' → fwdGlueIso {φ = φ i1} o (b i1 o'))) a1''
        ((unsafePOr δ ψ (λ {(δ = i1) → idp})
          ((λ{ (ψ = i1) → lemGlueIso {φ = φ i1} (λ _ → b i1 itIsOne) o })))))
      t1 α : PartialP (φ i1) _
      t1 o = proj₁ (g o)
      α o = proj₂ (g o)

      a1 = unsafeComp (λ j → A i1) (φ i1 ∨ ψ)
             (λ j → unsafePOr (φ i1) ψ (λ o → α o j) (a i1)) a1''

      b1 : Glue _ (φ i1) (T i1) (f i1)
      b1 = unsafeGlue {φ = φ i1} t1 a1
    b1 = Forall.b1 (FaceForall.δ φ) (FaceForall.∀e φ)

compGlue : {ℓ ℓ' : I → Level} (A : ∀ i → Set (ℓ i)) (φ : I → I)
           (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
           (f : ∀ i → PartialP (φ i) λ o → (T i o) → (A i)) →
           (pf : ∀ i → PartialP (φ i) (λ o → isEquiv (T i o) (A i) (f i o))) →
           let B : ∀ i → Set (ℓ' i)
               B = λ i → primGlue (A i) (φ i) (T i) (f i) (pf i)
           in  (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0) → B i1
compGlue A φ T f pf ψ b b0 =
  CompGlue.Local.b1 A φ T (λ i p → f i p , pf i p) ψ b b0

{-# BUILTIN COMPGLUE compGlue #-}
\end{code}}

\AgdaHide{
\begin{code}
module _ {ℓ} {A B : Set ℓ} where
\end{code}}

The other direction is harder. CuTT adds a primitive operation \F{Glue} that allows us to directly give \F{ua} in a manner similar to \F{comp}. In particular, \F{Glue} allows us to partially specify the following square ($i\in\D{I}$) where the top and bottom sides are paths but the left and right sides are equivalences, so that it can complete the missing bottom side---the desired path. The diagram and proof are taken from \href{https://github.com/mortberg/cubicaltt/blob/master/lectures/lecture4.ctt}{here}.
\begin{figure}[H]
\centering
\begin{tikzpicture}[->]
  \node at (0,0) (a)  {\Arg{A}};
  \node at (0,3) (b1) {\Arg{B}};
  \node at (3,0) (b2) {\Arg{B}};
  \node at (3,3) (b3) {\Arg{B}};

  \path
    (a)  edge         node[left]  {e}           (b1)
    (b1) edge         node[above] {$\F{idp}~i$} (b3)
    (a)  edge[dashed] node[below] {?}           (b2)
    (b2) edge         node[right] {\F{ide}}     (b3);
\end{tikzpicture}
\end{figure}
\begin{code}
  ua : A ≃ B → A ≡ B
  ua e i = Glue B _ (λ { (i = i0) → A; (i = i1) → B})
    λ { (i = i0) → e; (i = i1) → ide }
\end{code}
\end{proof}

The power of univalence is that coercing along a univalent path (that is, a path constructed with \F{ua}) applies the underlying equivalence. This rule holds propositionally, as seen below, and gives us our first example of a nondegenerate use of coercion.

\begin{code}
  ua-β : (e : A ≃ B) → coe (ua e) ≡ proj₁ e
  ua-β e = λ≡ λ x → coe-β _ ∙ coe-β _ ∙ coe-β _
\end{code}

Let's try a quick application given this knowledge. The \F{not} function is an equivalence on \F{Bool}, so coercing along this path with \Con{true} should evaluate to \Con{false}, which it does!

\begin{code}
open import Data.Bool using (Bool; true; false; not)

notq : Bool ≂ Bool
notq = not , mkqinv not
  (λ { true → idp; false → idp })
  (λ { true → idp; false → idp })

_ : coe (ua (qinvToEquiv notq)) true ≡ false
_ = idp
\end{code}

Did we do all this work for this one example? Of course not! Now, we get to good part---mathematics and programming with CuTT constructs.

\section{Mathematics}
Now that we have a minimal working library for cubical types, we can finally start doing something useful. Since CuTT, like its ``predecessor'' HoTT, models topological phenomena, it would be fitting to give a synthetic characterization of the \emph{fundamental group} of a space i.e. the group of paths with the constant path and composition, and investigate the fundamental group of the circle, a \emph{higher inductive type}. Thus, we must prove the following unit, inverse, and associativity laws. The base of our proofs is the left unit law.

\subsection{Fundamental Group}

\begin{theorem}
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y : A} where
\end{code}}
\begin{code}
  ∙-unitl : (p : Path x y) → idp ∙ p ≡ p
\end{code}
\end{theorem}
\begin{proof}
Recall that composition is defined in terms of \F{J}. Since we are applying the constant path, we can directly apply the propositional computation rule for \F{J}.
\begin{code}
  ∙-unitl = app≡ (J-β {P = λ y _ → Path x y → Path x y})
\end{code}
\end{proof}

The rest of the unit and inverse laws are direct corollaries of the left unit law.

\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y : A} where
\end{code}}
\begin{code}
  ∙-unitr : (p : Path x y) → p ∙ idp ≡ p
  ∙-unitr = J (λ _ p → p ∙ idp ≡ p) (∙-unitl idp)

  ∙-invl : (p : Path x y) → p ⁻¹ ∙ p ≡ idp
  ∙-invl = J (λ _ p → p ⁻¹ ∙ p ≡ idp) (∙-unitl idp)

  ∙-invr : (p : Path x y) → p ∙ p ⁻¹ ≡ idp
  ∙-invr = J (λ _ p → p ∙ p ⁻¹ ≡ idp) (∙-unitl idp)
\end{code}

Thus, it remains to show associativity.

\begin{theorem}
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y z w : A} where
\end{code}}
\begin{code}
  ∙-assoc : (p : Path x y) (q : Path y z) (r : Path z w) → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
\end{code}
\end{theorem}
\begin{proof}
By contracting $p$ to the constant path using \F{J}, we apply the left unit law on both sides.
\begin{code}
  ∙-assoc = J (λ _ p → ∀ q r → (p ∙ q) ∙ r ≡ p ∙ q ∙ r)
    λ q r → ap (λ x → x ∙ r) (∙-unitl q) ∙ ∙-unitl (q ∙ r) ⁻¹
\end{code}
\end{proof}

With all these results, we would like to make a definitive statement about some type being a group. In HoTT, we define the \emph{loop space} of $A$ to be the space of paths fixed at both ends on a given basepoint.

\begin{definition}[Loop space]
\begin{code}
Ω[_,_] : ∀ {ℓ} (A : Set ℓ) → A → Set ℓ 
Ω[ _ , a ] = Path a a
\end{code}
\end{definition}

Thus, we get the following result.

\begin{theorem}[Fundamental group]
For all $A$ and $a:A$, $Ω[A,a]$ is a group.
\end{theorem}

For our intents and purposes, we may treat the loop space exactly as the fundamental group; see page 207 of \cite{hottbook} for more details. Let us take a moment to appreciate the simplicity of these results---indeed, HoTT and CuTT are useful tools for topologists and homotopy theorists due to the ease of formalizing complex results.

\AgdaHide{
\begin{code}
{-
open import Algebra using (Group)

Ω-Group : ∀ {ℓ} (A : Set ℓ) → A → Group ℓ ℓ
Ω-Group A x = record
  { Carrier = Ω[ A , x ]
  ; _≈_ = _≡_
  ; _∙_ = _∙_
  ; ε = idp
  ; _⁻¹ = _⁻¹
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isEquivalence = PathIsEquivalence
        ; assoc = ∙-assoc
        ; ∙-cong = {!!} }
      ; identity = ∙-unitl , ∙-unitr }
    ; inverse = ∙-invl , ∙-invr
    ; ⁻¹-cong = {!!}
    }
  }
-}
\end{code}}

\subsection{Higher Inductive Types: The Circle}
Now that we have the vocabulary to discuss the fundamental group of various spaces, it behooves us to characterize that of a nontrivial space, like \emph{the circle}. Homotopically, a circle is simply a single basepoint \F{base} with a \emph{nonconstant} path \F{loop} from \F{base} back to itself, as illustrated in \ref{fig:circle} (figure 6.1 taken from \cite{hottbook}).

\begin{figure}[H]
\includegraphics[width=0.5\textwidth]{circle.png}
\centering
\label{fig:circle}
\end{figure}

We can characterize this concept in CuTT via a \emph{higher inductive type} \F{S¹}: not only is it inductively generated by $\F{base}$, but also by the path \F{loop}, which exists at a ``higher'' level than \F{base}. In general, any data type that defines its own paths is higher inductive. The circle has a \emph{topological recursion principle} \F{recS¹} that allows one to define a function $f:S^1\to A$ given the following data.

\begin{itemize}
\item A \F{base} case $b:A$
\item A \F{loop} case $l:b\equiv b$ 
\end{itemize}

Then, we are guaranteed the definitional equalities $f~\F{base}=b$ and $\F{ap}~f~\F{loop}=l$.

\AgdaHide{
\begin{code}
-- Rewrite relation and Circle from rrose/basic-hott
module RewriteRelation where

module _ {ℓ} {X : Set ℓ} where
  infix 30 _↦_
  postulate 
    _↦_ : X → X → Set ℓ
{-# BUILTIN REWRITE _↦_ #-}

postulate
  S¹ : Set
  base : S¹
  loop : Path base base

module RecS¹ {ℓ} {Y : Set ℓ}
             (base* : Y)
             (loop* : base* ≡ base*) where
  postulate
    f : S¹ → Y
    base-β : f base ↦ base*

  {-# REWRITE base-β #-}
  
  postulate
    loop-β : ∀ i → f (loop i) ↦ loop* i
    -- Saizan needed this...
    compr : ∀ {φ u u0} → (f (unsafeComp (λ i → S¹) φ u u0)) ↦
                           (unsafeComp (λ i → Y)
                                       φ
                                       (λ i → λ { (φ = i1) → f (u i itIsOne) }) (f u0))

  {-# REWRITE loop-β #-}
  {-# REWRITE compr #-}
   
recS¹ = RecS¹.f

open import Data.Integer hiding (_⊔_)
open import Data.Nat hiding (_⊔_)
\end{code}}

We would now like to show the following result.

\begin{theorem}
The fundamental group of the circle is the integers i.e. $\Omega[S^1,\F{base}]\equiv\mathbb{Z}$.
\end{theorem}
\begin{proof}
A proof by Dan Licata is given at \cite{licata2012fundgrp}. As we did with univalence, we will not discuss the homotopies, but the computational essence of the proof. The intuition is that we can ascribe a normal form to any path in $\Omega[S^1,\F{base}]$: it is either \F{idp}, $\F{loop}^n=\underbrace{\F{loop}\cdot\ldots\cdot\F{loop}}_n$, or $\F{loop}^{-n}=\underbrace{\F{loop}^{-1}\cdot\ldots\cdot\F{loop}^{-1}}_n$. These look remarkably like the integers---as a result, a map $\Omega[S^1,\F{base}]\to\mathbb{Z}$ sends \F{idp} to $0$, $\F{loop}^n$ to $n$, and $\F{loop}^{-n}$ to $-n$. Then, the quasi-inverse simply takes an integer $n$ and iterates \F{loop} $n$ times in the direction of its sign, or \F{idp} if $n=0$.
\end{proof}

The easier direction is actually backwards---giving the map from $\mathbb{Z}$ to $\Omega[S^1,\F{base}]$.

\begin{definition}[Winding path]
\begin{code}
loop^ : ℤ → Ω[ S¹ , base ]
loop^ (+ 0)        = idp
loop^ (+ suc n)    = loop ∙ loop^ (+ n)
loop^ -[1+ 0 ]     = loop ⁻¹
loop^ -[1+ suc n ] = loop ⁻¹ ∙ loop^ -[1+ n ]
\end{code}
\end{definition}

The hard part is going forwards---how do we inspect the normal form of a path? We cannot do it directly, but we can do it with the topological recursion principle. First, we quickly prove that the successor function on the integers is an equivalence with the predecessor function as its quasi-inverse.

\begin{code}
suc≡ : ℤ ≡ ℤ
suc≡ = ua $ qinvToEquiv
  (Data.Integer.suc ,
   mkqinv Data.Integer.pred
   (λ { (+ _) → idp; -[1+ 0 ] → idp; -[1+ suc _ ] → idp })
   (λ { (+ 0) → idp; (+ suc _) → idp; -[1+ _ ] → idp }))
\end{code}

We now define the \emph{universal cover} of the circle, which sends \F{base} to $\mathbb{Z}$ and satisfies $\F{ap}~\F{Cover}~\F{loop}=\F{suc\equiv}$.

\begin{definition}[Universal cover of the circle]
\begin{code}
Cover : S¹ → Set
Cover = recS¹ ℤ suc≡
\end{code}
\end{definition}

We finally give the desired map, which computes the \emph{winding number} of a given path.

\begin{definition}[Winding number]
Recall that $\F{transport}~P=\F{coe}\circ\F{ap}~P$. Since $\F{ap}~\F{Cover}~\F{loop}\equiv\F{suc\equiv}$, it follows that by the propositional computation rule \F{ua-β}:

$$\F{coe}~(\F{ap}~\F{Cover}~\F{loop})~0\equiv\F{coe}~(\F{suc\equiv})\equiv\F{suc}~0=1$$

Furthermore, $\F{coe}~(\ldots)~\F{idp}~0\equiv 0$ by the propositional computation rule \F{coe-β}. We get the general case for $\F{loop}^n$ and $\F{loop}^{-n}$ by the functoriality of \F{transport} and \F{ua}:

\begin{enumerate}
\item $\F{transport}~\F{Cover}~\F{loop}^n~0\equiv(\F{transport}~\F{Cover}~\F{loop})^n~0\equiv\F{suc}^n~0\equiv n$
\item $\F{transport}~\F{Cover}~\F{loop}^{-n}~0\equiv\left((\F{transport}~\F{Cover}~\F{loop})^{-1}\right)^{n}~0\equiv\left((\F{suc}\equiv)^{-1}\right)^{n}~0\equiv\F{pred}^n~0\equiv -n$
\end{enumerate}

Thus, we give the following definition.

\begin{code}
w : Ω[ S¹ , base ] → ℤ
w p = transport Cover p (+ 0)
\end{code}
\end{definition}

\section{Programming}
Dan Licata gave a talk titled \emph{Programming in Homotopy Type Theory} \cite{licata2012} in which he expounded upon the applications of univalence to software engineering. In particular, univalence does not allow a type theory to distinguish between equivalent types, so we can safely interchange use between them when convenient. This greatly increases code reuse---given code for one type, we can automatically generate code for all other equivalent types without resorting to metaprogramming or other ad hoc facilities. Furthermore, we can specify the behavior of one type and yield similar proofs of behavior for other equivalent types with the same mechanism. Consider the following examples.

\subsection{Code Reuse}
In Haskell and other functional programming languages, map/reduce algorithms are common when manipulating and consolidating data. Formally speaking, given a stream of data belonging to a monoid, we can ``reduce'' it via its associative operation.

\begin{definition}[Monoid]
A monoid is a type equipped with an identity element and associative operation.
\begin{code}
record Monoid {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  infixr 7 _·_
  field
    e : A
    _·_ : A → A → A
    ·-unitl : ∀ x → (e · x) ≡ x
    ·-unitr : ∀ x → (x · e) ≡ x
    ·-assoc : ∀ x y z → (x · y · z) ≡ ((x · y) · z)
\end{code}
\end{definition}

\AgdaHide{
\begin{code}
open Monoid {{...}} public
open import Data.List using (List; []; _∷_; _++_; length)
\end{code}}

\F{foldl} performs this reduction operation on a finite stream from left-to-right.

\begin{code}
foldl : ∀ {ℓ} {A : Set ℓ} {{M : Monoid A}} → List A → A
foldl []       = e
foldl (h ∷ t) = h · foldl t
\end{code}

Clearly, lists---the free monoid over any type---is a monoid. In fact, we give its instance of \F{Monoid} with the empty list as the identity element and ``append'' as the associative operation.

\begin{code}
instance
  ListMonoid : ∀ {ℓ} {A : Set ℓ} → Monoid (List A)
  ListMonoid {A = A} = record
    { e       = []
    ; _·_     = _++_
    ; ·-unitl = λ _ → idp
    ; ·-unitr = unitr
    ; ·-assoc = assoc } where

    unitr : (l : List A) → (l ++ []) ≡ l
    unitr []       = idp
    unitr (h ∷ t) = ap (_∷_ h) (unitr t)

    assoc : (x y z : List A) → (x ++ y ++ z) ≡ ((x ++ y) ++ z)
    assoc []       _ _ = idp
    assoc (h ∷ t) y z = ap (_∷_ h) (assoc t y z)
\end{code}

This proof was quite tedious, but wait! It turns out that \emph{vectors}---lists indexed by length---behave \emph{exactly} like lists, so if the programmer would like to get the same functionality out of vectors, they would have to do essentially the same proof all over again...This is of course, a total waste of time. What if there was a way to generate the same \F{Monoid} instance for vectors given the one we have for lists? With univalence and \F{transport}, there is! First, consider the following datatype, which uses existential quantification to enclose over the type index for length.

\begin{code}
open import Data.Vec using (Vec; []; _∷_; fromList; tabulate; map; _[_]=_; here; there)

VecList : ∀ {ℓ} → Set ℓ → Set ℓ
VecList A = Σ ℕ (Vec A)
\end{code}

Now, we can state the intuitively obvious univalent path: lists are equivalent to vectors. We do so by converting lists to vectors and vice versa element-by-element, which preserves length.

\begin{code}
ListIsVecList : ∀ {ℓ} {A : Set ℓ} → List A ≡ VecList A
ListIsVecList {A = A} = ua (qinvToEquiv (toVecList , mkqinv toList ε η)) where
  toVecList : List A → VecList A
  toVecList l = length l , fromList l

  toList : VecList A → List A
  toList (_ , v) = Data.Vec.toList v

  ε : (toList ∘ toVecList) ∼ id
  ε []       = idp
  ε (h ∷ t) = ap (_∷_ h) (ε t)

  η : (toVecList ∘ toList) ∼ id
  η (_ , [])         = idp
  η (suc n , h ∷ t) = ap (λ{(n , t) → ℕ.suc n , h ∷ t}) (η (n , t))
\end{code}

Now here is the cool part: we get an instance of \F{Monoid} for \F{VecList} for free, as desired. The indiscernibility of identicals is not only a statement about propositions, but for \emph{type-level functions}. Since \F{Monoid} is such a function, we can transport \F{ListMonoid} along the above path to yield the following instance.

\begin{code}
instance
  VecListMonoid : ∀ {ℓ} {A : Set ℓ} → Monoid (VecList A)
  VecListMonoid = transport Monoid ListIsVecList ListMonoid
\end{code}

The utility and simplicity of this design pattern is astonishing---having a typesafe method of code generation will surely make sophisticated type theories more attractive to software engineers.

\subsection{Abstract Types}
Let us consider a similar application of univalence as in the last section. In particular, we often have different type-level views of the same concept. For example, in programming languages, typing contexts can simultaneously be thought of as functions from a domain of variables to a codomain of types, or a set of ordered pairs between variables and types. Informally, we do not make a distinction between them, but contemporary type theories do, making formal reasoning in a proof assistant cumbersome. While this does not bother a lot of practitioners, this is a fundamental disconnect between the way we reason about mathematical objects versus the language we use to represent them. Philosophically, a univalent type theory is much better suited to mathematics and software engineering, because once again, it cannot distinguish between equivalent concepts, as we do not. Thus, consider extending the above example: another way to view vectors is as \emph{arrays}---an array of length $n$ with elements in $A$ is a function from the set $\{0,\ldots,n-1\}$ to $A$, as follows.

\begin{code}
open import Data.Fin using (Fin; zero; suc)

Array : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
Array A n = Fin n → A
\end{code}

\AgdaHide{
\begin{code}
lookup : ∀ {ℓ n} {A : Set ℓ} → Vec A n → Array A n
lookup = flip Data.Vec.lookup
\end{code}}

Lists, vectors, and arrays are all \emph{functors}, inspired by the analogous category-theoretic concept. Functors are types equipped with a map operation \'a la map/reduce that obeys the identity function and function composition.

\begin{code}
record Functor {ℓ₁} {ℓ₂} (F : Set ℓ₁ → Set ℓ₂) : Set (lsuc ℓ₁ ⊔ ℓ₂) where
  infixl 4 _<$>_
  
  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    <$>-id : ∀ {A} (a : F A) → (id <$> a) ≡ a
    <$>-∘ : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) →
      ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))
\end{code}

\AgdaHide{
\begin{code}
open Functor {{...}} public
\end{code}}

Now, here is our scenario: it is \emph{much} easier to reason about arrays than vectors because as functions, we can explicitly reason about the shape of each element. On the other hand, vectors are more easily memory optimized since they do not close on the environment like a function does at runtime. It follows that wherever we can, we reason about arrays, and then transport equivalent results to vectors. For example, consider the trivial \F{Functor} instance for arrays.

\begin{code}
instance
  ArrayFunctor : ∀ {ℓ n} → Functor {ℓ} (flip Array n)
  ArrayFunctor = record
    { _<$>_  = λ f a i → f (a i)
    ; <$>-id = λ _     → idp
    ; <$>-∘  = λ _ _ _ → idp }
\end{code}

Let us consider how arrays and vectors are equivalent. We can convert an array to a vector by tabulating it from $0$ to $n-1$. and vice versa by constructing a function that looks up a value by index from the given vector.

\begin{code}
ArrayIsVec : ∀ {ℓ} (A : Set ℓ) (n : ℕ) → Array A n ≡ Vec A n
ArrayIsVec A n = ua (qinvToEquiv (tabulate , mkqinv lookup ε η)) where
  ε : (lookup ∘ tabulate) ∼ id
  ε f = λ≡ h where
    h : ∀ {n} {f : Array A n} → lookup (tabulate f) ∼ f
    h zero    = idp
    h (suc x) = h x

  η : ∀ {n} → (tabulate ∘ lookup {n = n}) ∼ id
  η []       = idp
  η (h ∷ t) = ap (_∷_ h) (η t)
\end{code}

Finally, we can automatically generate an instance of \F{Functor} for vectors and export a proof that the generated definition for the map operation obeys the identity function.

\begin{code}
instance
  VecFunctor : ∀ {ℓ n} → Functor {ℓ} (flip Vec n)
  VecFunctor {n = n} = transport Functor (λ≡ (flip ArrayIsVec n)) (ArrayFunctor {n = n})

_ : ∀ {ℓ₁} {A : Set ℓ₁} {n} (v : Vec A n) → Functor._<$>_ VecFunctor id v ≡ v
_ = Functor.<$>-id VecFunctor
\end{code}

While this is nice, it would be more powerful to reason about \emph{existing} definitions and not generated ones. Licata discusses an example where we have two views of sequences---\F{ListSeq}s with an operationally sequential map operation, and \F{PSeq}s with an operationally parallel one. \href{https://github.com/dlicata335/hott-agda/blob/master/programming/Sequence.agda}{Here} is a link where he formalizes, in homotopy type theory, the ability to extract a proof that \F{PSeq}'s map function is coherent from an equality between \F{ListSeq} and \F{PSeq} as well as a proof of coherence for \F{ListSeq}'s map function.

\section{Conclusion and Future Work}
The power of cubical type theory lies in an alternative view of equality that has clear benefits to mathematics and programming---in general, we have demonstrated to ourselves that type theory is both a powerful foundations of mathematics and programming language. Not only does it have the potential to change the way we do math by realigning formalism with our intuitions about computation and equality, it could be the start of a class of programming tools that ends the many pain points of structuring software. It remains to develop type theory and proof assistants with univalent principles to a point where they become usable as daily drivers for mathematicians and software engineers alike.

\nocite{*}
\bibliographystyle{acm}
\bibliography{references}

\end{document}
