# Supplementary Material: NumLogV2 Documentation
The is an extended version of NumLog
**Source Repository:** [https://github.com/hmlr-lab/NumLog](https://github.com/hmlr-lab/NumLog)

## 1. Overview
**NumLogV2** is a hybrid Inductive Logic Programming (ILP) system designed for learning and reasoning with numerical data. Developed by the HMLR lab, it builds upon traditional ILP techniques by integrating **Gaussian Mixture Models (GMM)** to cluster numerical values and automatically invent numerical predicates. This enables the system to handle complex, non-discrete numerical constraints natively during the logic learning phase.

### 1.1 Core Capabilities
*   **Numerical Clustering via GMMs**: Probabilistically distinguishes between positive and negative numerical examples using Gaussian probability density functions.
*   **Predicate Invention**: Dynamically creates new predicates encapsulating complex numerical boundaries.
*   **Bottom Clause Generation**: Implements a robust clause saturation algorithm tied to background knowledge (BK).
*   **C++ Acceleration**: Offloads computationally expensive relational and GMM thresholding tasks to an external C++ library (`libnumlogV2.so`).

---

## 2. Dependencies and Operators
NumLogV2 relies on SWI-Prolog and several libraries:
*   `library(clpfd)`: Constraint Logic Programming over Finite Domains.
*   `library(assoc)`: Association lists for efficient variable mapping.
*   `libnumlogV2.so`: A foreign C++ library that handles numeric relations (`findRelations/3`) and GMM thresholding (`findThresholds/4`).

**Custom Operators:**
The system defines several custom operators to elegantly represent Gaussian parameters and numerical bindings directly in the logic syntax:
*   `μ` (Mean) and `σ` (Standard Deviation)
*   `#` (Numeric constraint identifier)
*   `=>` (Relational implication)

---

## 3. Main Workflow
The primary entry point of the system is the `learnFromFile/3` predicate. 

### `learnFromFile(+BKFile, +ExampleFile, +BiasFile)`
This is the main execution pipeline. It takes three input files (Background Knowledge, Examples, and Bias/Mode Declarations) and performs the following sequence:
1.  **Initialization**: Consults the input files and extracts dynamic `modeh/2` (head declarations) and `modeb/2` (body declarations).
2.  **Example Segregation**: Separates positive (`pos/1`) and negative (`neg/1`) examples.
3.  **Saturation**: Generates bottom clauses (`BCs`) for both positive and negative examples via `generateBottomClause/3`.
4.  **Numerical Analysis**: Invokes `analyseNumbers/5` to group variables by numeric values, passing them to the GMM clustering algorithm to invent boundary functions and numerical relations.
5.  **Hypothesis Generation**: Iterates over the bottom clauses to generate a hypothesis space via `hypothesisSpace/6`.
6.  **Rule Selection**: Evaluates the generated rules against coverage metrics to find the optimal rule (`findBestRules/3`).

---

## 4. Key Components and Predicates

### 4.1 Gaussian Mixture Models (GMM) Evaluation
Instead of static numerical ranges, NumLogV2 uses probabilistic scoring. 

*   **`gaussian_pdf(+X, +(μ(Mean), σ(Var)), -Score)`**
    Calculates the probability density function score for a given numerical value `X` against a Gaussian distribution defined by its mean (`Mean`) and variance (`Var`). Uses a standard Gaussian exponentiation equation, with a fallback for extremely low variance (`Var =< 1e-6`).
*   **`inCluster(+X, +pos(PosGauss), +neg(NegGauss))`**
    Evaluates whether a numeric value `X` belongs to the positive cluster. It calculates the maximum PDF score among the positive GMMs and compares it to the maximum PDF score among the negative GMMs.

### 4.2 Numerical Analysis & Predicate Invention
NumLogV2 handles numbers by intercepting them during clause generation and building dynamic thresholds.

*   **`analyseNumbers(+Pos, +Neg, -InventedFunctions, -Relations, -NewBC)`**
    Flattens and clusters positive and negative examples based on their numerical arguments. It leverages `cppRelations/2` (communicating with the foreign library) to discover numerical relations. Finally, it triggers `extractAndProcessGMM/4` to invent functions representing numerical bounds.
*   **`extractAndProcessGMM(+PosData, +NegData, +Acc, -FunctionsInvention)`**
    Aligns positive and negative continuous data. It relies on the external `findThresholds` function to yield positive and negative clusters (`[Mean, StdDev]`). It converts these clusters into prolog operators (`μ`, `σ`) and dynamically constructs a new clause body wrapped in the `inCluster/3` predicate.

### 4.3 Clause Generation & Refinement
*   **`generateBottomClause(+Examples, +Acc, -BottomClauses)`**
    Iterates through examples, utilizing `bottomClause/5` to extract predicates based on the arity and type declarations (`in`, `out`, `const`, `numeric`) defined in the bias file.
*   **`refinementBottomClauses/5`**
    Trims and organizes bottom clauses by matching expected numeric patterns. It constructs `relations` wrappers around variables that are associated with numeric constraints.

### 4.4 Hypothesis Generation and Coverage
*   **`hypothesisSpace(+Exs, +NExs, +InvF, +Relations, +BCs, -Rules)`**
    Generates rule combinations up to a length specified by the combinations logic (defaulted to size 4 subsets of the bottom clause literals). Uses `head_connectedness/2` to ensure variables in the body are logically linked to the head clause.
*   **`checkCoverage(+Clause, +InvF, +Rel, +Pos, +Neg, -Rule)`**
    Dynamically asserts a newly formed hypothesis clause, alongside its invented functions (`InvF`) and relations (`Rel`). It uses `entailExamples/3` to count how many positive and negative examples are successfully entailed by the current hypothesis.

---

## 5. Foreign Function Interface (C++ Library)
NumLogV2 relies on `libnumlogV2.so` for heavy computational tasks. While not defined in the Prolog script, the Prolog engine expects the following interfaces:
1.  **`findThresholds(PosList, NegList, PosCluster, NegCluster)`**: Computes the optimal GMM split for continuous data, returning pairs of Means and Variances.
2.  **`findRelations(Terms, Values, Relations)`**: Computes algebraic relations between variables rapidly using C++ matrix/vector operations.

---

## 6. Language and Syntax Constructs
Variables mapped to constants are managed via Association Lists (`library(assoc)`) to ensure consistency across the generated hypothesis space (e.g., `count_vars/2`, `single_occurrence_vars/1`). `restore_vars/2` allows NumLogV2 to map ground atoms back to Prolog variables safely before evaluation, guaranteeing that structural bindings are retained during coverage checking.
