
```markdown
# 3n+1 Analysis Framework Formalization Project 

Welcome to the 3n+1 Analysis Framework Formalization Project,  a formalization effort of the 3n+1 conjecture using the Coq proof assistant.
This repository includes the ongoing work and original idea files.
The project includes original and immature idea files, which contain various versions of doc documents.
 We have used Coq code to formalize and verify these ideas. The main formalization code is located in the /coq_prj1/ directory.

## Overview
# The Collatz Conjecture

The Collatz Conjecture, also known as the 3n+1 Conjecture or the Iceberg Conjecture, is an unresolved mathematical problem that is widely
recognized for its difficulty and complexity in the mathematical community.

![Collatz Conjecture](https://upload.wikimedia.org/wikipedia/commons/7/72/Collatz-problem.svg)

## Simplicity and Difficulty of Solution

The statement of the Collatz Conjecture is remarkably simple: for any positive integer $n$, by repeatedly applying the rule that if $n$ is even,
divide it by 2, and if $n$ is odd, multiply it by 3 and add 1, the sequence will eventually reach the number 1. However, despite the problem
being easy to understand, proving or refuting it has proven to be exceptionally challenging.

## Long-standing Unsolved Problem

Since its proposal by Lothar Collatz in the 1930s, the Collatz Conjecture has remained unsolved for over 60 years. Mathematician Paul Erdős
 once stated, "Mathematics is not yet ready for such problems," and all evidence to date suggests he was correct.

## Behavior of Dynamical Systems

The behavior of the dynamical systems involved in the Collatz Conjecture makes proving or refuting the conjecture extremely difficult.
Researchers have attempted to analyze the upper bounds of divergent trajectories, patterns of iteration counts for specific operations,
and extend the mapping to a continuous version on the real number line.

## Limitations of Computer Verification

Although computers have verified that all positive integers less than $2^{68}$ (approximately $2.9 \times 10^{20}$) conform to the Collatz Conjecture,
 this is not sufficient to prove the conjecture for all positive integers.

## Views of Mathematical Masters

Mathematician Paul Erdős offered a \$500 prize in 1983 for anyone who could prove or refute the Collatz Conjecture.
He himself considered it an "extremely difficult problem, completely beyond the capabilities of contemporary mathematics.
" The exploration of the Collatz Conjecture has involved many mathematicians' contributions.
 For instance, German mathematician Lothar Collatz was interested in iterative functions in the 1930s, and in the 1950s and 1960s,
through mathematicians such as Helmut Hasse and Shizuo Kakutani, it spread to various universities, including Syracuse University.

## Contribution of Terence Tao

In 2019, mathematician Terence Tao made significant progress in the study of the Collatz Conjecture. He proved that almost all (99.99% or more)
starting values eventually reach numbers below 200, and since it is known that every starting value up to 200 eventually reaches 1, at least 99.99%
 of all positive integers conform to the Collatz Conjecture.

In summary, the difficulty of the Collatz Conjecture lies in the complex dynamic behavior hidden behind its simple rules and the failure to
 find a general method to prove or refute it to date. Additionally, the Collatz Conjecture is related to other important problems in mathematics,
such as iterative functions in dynamical systems. Although the conjecture can be computationally verified for specific numbers,
 proving it for all positive integers is very difficult.

Based on existing original ideas, we have mainly adopted combinatorial analysis methods, using some computational tools to observe numerical sequences,
 first generating some original ideas, constructing sequences, and attempting to formalize them strictly,
finally finding some effective paths to describe sequence properties and expand to the global context. In terms of methodology,
we first combined the local properties of the sequence into a triangular undirected graph, then re-decomposed the undirected graph
to obtain theorems about the properties of the sequence.

## About this research:

In this study, we obtained dozens of local and global properties of the Collatz sequence, and established a series of theorems
 and necessary lemmas using the COQ proof tool, such as the main composition theorem about sequence patterns, theorems related
to the generation forms of sequence patterns, theorems on the decomposability and combinability of sequences, upper bound theorems
 and precise numerical upper bound theorems for sequence patterns, continuity and preservation theorems for sequence patterns,
 and the 3n+1 increment principle in the sequence (R0_count_grows_with_length), which may greatly assist in the study of the dynamics
 and numerical optimization of this problem.

![Collatz Sequence](https://upload.wikimedia.org/wikipedia/commons/3/3c/Collatz-sequence.png)
## Getting Started

To get started with the project, follow these steps:

1. **Prerequisites**: Ensure you have Coq and any necessary dependencies installed on your system.
2. **Clone the Repository**: Clone this repository to your local machine using the following command:
   ```
   git clone https://github.com/noya2012/collatz-prof1.git
   ```
3. **Compile the Project**: Navigate to the project directory and compile the Coq files using the Coq compiler.

## Directory Structure
/coq_prj1


## Contributing

We welcome contributions to this project! If you're interested in contributing, please follow these guidelines:

1. **Fork the Repository**: Fork this repository to your GitHub account.
2. **Create a Branch**: Create a new branch for your changes.
3. **Commit Your Changes**: Commit your changes with a clear message describing the updates.
4. **Push and Submit a Pull Request**: Push your changes to your fork and submit a pull request to the main repository.

## License

This project is licensed under the [Apache License 2.0](LICENSE). You are free to modify and distribute the source code,
as long as you include the required notices and do not mislead others about the origin of the project.

## Contact

For any questions or inquiries, please reach out to the project maintainer:
  JIA NING ZENG
- [noya2012](mailto:noya2012@126.com)
- BACKUP MAILBOX (mailto:306000250@QQ.COM)
  orcid：0000-0003-1338-9978

Thank you for your interest in the 3n+1 Analysis Framework Formalization Project (Collatz Prof1)!
```


