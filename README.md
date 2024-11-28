
```markdown
# The Combinatorial Analysis Framework of the 3N + 1 Conjecture - COQ Formalization Project

Welcome to this 3n+1 Analysis Framework Formalization Project,
As indicated in the title, this is a project that studies the 3n + 1 conjecture
using combinatorial methods and conducts formal verification in the form of Coq code.

The main formalization code is located in the /coq_prj1/ directory.

## Overview
The Collatz Conjecture, also known as the Hailstone Conjecture, is an unsolved mathematical problem, and its difficulty
 and complexity are widely recognized in the mathematical community.

1. **The Simplicity of the Problem and the Difficulty of Solving It**: The statement of the Collatz Conjecture is extremely simple.
That is, for any positive integer n, by repeatedly applying the following rule: if n is even, divide it by 2; if it is odd, multiply
 it by 3 and then add 1. Eventually, it will reach the number 1. However, although the problem is easy to understand, its proof or
refutation is exceptionally difficult.

2. **Long-Term Unsolved**: Since the Collatz Conjecture was proposed by Lothar Collatz in the 1930s, it has remained unsolved for more
 than 60 years. The mathematician Paul Erdős once said, "Mathematics is not yet ready to handle such a problem," and all the evidence
 so far indicates that he was right.

3. **The Behavior of the Dynamical System**: The behavior of the dynamical system involved in the Collatz Conjecture makes it
extremely difficult to prove or refute the conjecture. Researchers have attempted to conduct research by analyzing the growth upper bound
 of divergent trajectories, the pattern of the number of iterations of specific operations, and extending this mapping to a continuous
version on the real line.

4. **The Limitations of Computer Verification**: Although computers have verified that all positive integers less than 2^68
 (approximately 2.9 × 10^20) conform to the Collatz Conjecture, this is not sufficient to prove that the conjecture holds for
 all positive integers.

5. **The Views of Mathematical Masters**: In 1983, the mathematician Paul Erdős offered a $500 prize to anyone who could prove
 or refute the Collatz Conjecture. He himself considered it "an extremely difficult problem, completely beyond the capabilities of
contemporary mathematics." The exploration of the Collatz Conjecture in history has included the contributions of many mathematicians.
 For example, the German mathematician Lothar Collatz was interested in iterative functions in the 1930s and spread it to various
universities, including Syracuse University, through Helmut Hasse and Shizuo Kakutani and others in the 1950s and 1960s.

6. **The Contribution of Terence Tao**: In 2019, the mathematician Terence Tao made significant progress in the research of the
Collatz Conjecture. He proved that almost all (99.99% or more) starting values will eventually reach values below 200, and since
it is known that each starting value up to 200 will eventually reach 1, at least 99.99% of all positive integers conform to the
 Collatz Conjecture.

In conclusion, the difficulty of the Collatz Conjecture lies in the complex dynamical behavior hidden behind its simple rules and
the fact that a general method to prove or refute it has not been found so far.
Moreover, the Collatz Conjecture is related to other important problems in mathematics, such as iterative functions in dynamical
systems. Although this conjecture can be verified by calculation for specific numbers, it is very difficult to prove that it holds
for all positive integers.

Based on the existing original ideas, we mainly adopted the combinatorial analysis method.
We used some computational tools to observe numerical sequences and first generated some original ideas,
which can be found in the docx file in this directory.
Then, we constructed sequences according to the original ideas and tried to make them rigorous. Methodologically,
we first combined the local properties of the sequences into a triangular undirected graph, and then re-decomposed
the undirected graph to obtain the property theorems of the sequences.

Regarding This Research
The project includes original and immature idea files, which contain various versions of doc documents.
 We have used Coq code to formalize and verify these ideas.
In this research, we obtained dozens of local and global properties of the Collatz sequences. Using the Coq proof assistant,
 we established a series of theorems and necessary lemmas, such as the main composition theorem about the sequence pattern,
the related theorem about the generation form of the sequence pattern, the decomposable and combinable theorem of the sequence,
 the upper bound theorem of the sequence pattern and the exact numerical upper bound theorem, the pattern continuity
and preservation theorem, and the principle of the increasing number of R0 operations in the sequence (R0_count_grows_with_length).
 These may bring great help to the research on the dynamics and numerical optimization of this problem.


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
- Orcid：0000-0003-1338-9978

Thank you for your interest in The Combinatorial Analysis Framework of the 3N + 1 Conjecture - COQ Formalization Project!
## Links
-zulip https://caf3np1.zulipchat.com/join/o7x6krw77psfytm74b3ihq2h/

-Other Recommended Formalization Projects

  Fermat's Last Theorem Formalization Project
  1.https://github.com/ImperialCollegeLondon/FLT
  2.https://gitcode.com/gh_mirrors/fl/FLT
                                                      
```


