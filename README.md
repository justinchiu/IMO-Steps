# Lemmas Dataset
Lemmas dataset is a benchmark that consists of building blocks for 13 IMO problems. The topics cover a variety of concepts ranging from divisibility to finite sets and functions. All proof steps are written in Lean 4. 

The purpose of the dataset is to expose current theorem provers' ability in solving IMO problems and highlight their strengths and weaknesses.

The dataset is released under MIT license. Contributions are welcome through pull requests.

## Performance of SOTA LLMs on the Lemmas Dataset
| Problem | # of lemmas | DeepSeek Prover-v1.5-RL (@32)             | Goedel-Prover (@32)                       | ReProver retrieval ✗     | ReProver retrieval ✓     | o3-mini (with 10 e.f.) |
|:---------:|:--------------:|:-------------------------------------------:|:-------------------------------------------:|:-------------------------------:|:-------------------------------:|:-------------------------------:|
| 1959-p1 | 4            | 3 (75.0\%)                    | 2 (50.0\%)                                | 2 (50.0\%)                    | 2 (50.0\%)                    | 2 (50.0\%)  |
| 1960-p2 | 9            | 7 (77.8\%)                    | 6 (66.7\%)                                | 3 (33.3\%)                    | 4 (44.4\%)                    | 1 (11.1\%)   |
| 1962-p2 | 14           | 13 (92.9\%) | 12 (85.7\%)             | 7 (50.0\%)                    | 8 (57.1\%)                    | 6 (42.9\%)                    |
| 1964-p2 | 9            | 5 (55.6\%)                    | 5 (55.6\%)                    | 5 (55.6\%)        | 5 (55.6\%)        | 3 (33.3\%)                    |
| 1965-p2 | 73           | 48 (65.8\%)                   | 47 (64.4\%)                               | 47 (64.4\%) | 46 (63.0\%) | 12 (16.4\%)                   |
| 1983-p6 | 53           | 25 (47.2\%)                               | 32 (60.4\%)                   | 28 (52.8\%)                   | 29 (54.7\%)                   | 18 (34.0\%)                   |
| 1984-p6 | 64           | 31 (50.0\%)                               | 33 (51.6\%)                   | 25 (39.1\%)                   | 24 (37.5\%)                   | 13 (20.3\%)                   |
| 1985-p6 | 427          | 116 (27.2\%) | 116 (27.2\%) | 89 (20.8\%)  | 89 (20.8\%)  | 84  (19.7\%)                  |
| 1992-p1 | 91           | 48 (52.7\%)                               | 54 (59.3\%)                   | 35 (38.5\%)                   | 34 (37.4\%)                   | 25 (27.5\%)                   |
| 1997-p5 | 122          | 51 (41.8\%)                   | 49 (40.2\%)                               | 48 (39.3\%)                   | 51 (41.8\%)       | 30 (24.6\%)                   |
| 2022-p2 | 61           | 34 (55.7\%)                   | 30 (49.2\%)                               | 24 (39.3\%)                   | 25 (41.0\%)                   | 25 (41.0\%)                   |
| 2022-p5 | 265          | 89 (33.6\%)                   | 76 (28.7\%)                               | 80 (30.2\%)                   | 77 (29.1\%)                   | 60 (22.6\%)                   |
| 2023-p4 | 137          | 52 (38.0\%)                   | 41 (29.9\%)                               | 43 (31.4\%)                   | 45 (32.8\%)                   | 37 (27.0\%)                   |
| Total   | 1,329        | 522 (39.3\%)                  | 504 (37.9\%)                              | 436 (32.8\%)                  | 439 (33.0\%)                  | 316 (23.8 \%)                 |

## Distribution of Proof Length of LLM-Generated Proofs

## Citation
The dataset, motivations and additional results are available [here](https://openreview.net/forum?id=CrKMqRAhBo)
```
@article{
anonymous2024a,
title={A Lean Dataset for International Math Olympiad: Small Steps towards Writing Math Proofs for Hard Problems},
author={Anonymous},
journal={Submitted to Transactions on Machine Learning Research},
year={2024},
url={https://openreview.net/forum?id=CrKMqRAhBo},
note={Under review}
}
```
## Versioning
The Lemmas Dataset is explicitly written for the latest available Lean4 version at the moment - v4.17.0. Any subsequent release can impact the 

## Formalised IMO Problems Statistics
| #     | Year | Problem | Topic         | in miniF2F | Lean proof publicly available | # of lemmas | # of lines of Lean4 proof |
|:-------:|:------:|:---------:|:---------------:|:------------:|:-------------------------------:|:-------------:|:---------------------------:|
| 1     | 1959 | p1      | number theory | Yes        | Yes                           | 4           | 9                         |
| 2     | 1960 | p2      | algebra       | Yes        | Yes                           | 9           | 40                        |
| 3     | 1962 | p2      | algebra       | Yes        | No                            | 14          | 60                        |
| 4     | 1964 | p2      | algebra       | Yes        | Yes                           | 9           | 50                        |
| 5     | 1965 | p2      | algebra       | Yes        | No                            | 73          | 210                       |
| 6     | 1983 | p6      | algebra       | Yes        | No                            | 53          | 180                       |
| 7     | 1984 | p6      | number theory | Yes        | No                            | 64          | 380                       |
| 8     | 1985 | p6      | number theory | Yes        | No                            | 427         | 1,310                     |
| 9     | 1992 | p1      | number theory | Yes        | No                            | 91          | 480                       |
| 10    | 1997 | p5      | number theory | Yes        | No                            | 122         | 390                       |
| 11    | 2022 | p2      | algebra       | No         | No                            | 61          | 260                       |
| 12    | 2022 | p5      | number theory | No         | No                            | 265         | 640                       |
| 13    | 2023 | p4      | number theory | No         | No                            | 137         | 450                       |
|       | total|         |               |            |                               | 1,329       | 4,459                     |

## Additional Analysis of o3-mini Generated Proofs
| \#    | Problem | \# of lemmas | Correct proof in NL | Correct proof in Lean | Match between NL and Lean |
|:-----:|:-------:|:------------:|:-------------------:|:---------------------:|:-------------------------:|
| 1     | 1959-p1 | 4            | 100\%               | 50.0\%                | 100\%                     |
| 2     | 1960-p2 | 9            | 55.6\%              | 11.1\%                | 100\%                     |
| 3     | 1962-p2 | 14           | 92.9\%              | 42.9\%                | 100\%                     |
| 4     | 1964-p2 | 9            | 77.8\%              | 33.3\%                | 100\%                     |
| 5     | 1965-p2 | 73           | 97.3\%              | 16.4\%                | 100\%                     |
| 6     | 1983-p6 | 53           | 64.2\%              | 34.0\%                | 100\%                     |
| 7     | 1984-p6 | 64           | 73.4\%              | 20.3\%                | 100\%                     |
| 8     | 1985-p6 | 427          | 75.2\%              | 19.7\%                | 95.6\%                    |
| 9     | 1992-p1 | 91           | 87.6\%              | 27.5\%                | 100\%                     |
| 10    | 1997-p5 | 122          | 69.7\%              | 24.6\%                | 100\%                     |
| 11    | 2022-p2 | 61           | 77.0\%              | 41.0\%                | 100\%                     |
| 12    | 2022-p5 | 265          | 63.4\%              | 22.6\%                | 92.8\%                    |
| 13    | 2023-p4 | 137          | 88.3\%              | 27.0\%                | 92.7\%                    |
|       |  total  | 1,329        | 75.5\%              | 23.8\%                | 96.4\%                    |
