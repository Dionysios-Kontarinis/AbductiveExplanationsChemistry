AbductiveExplanationsChemistry
===============================

This project proposes a way to reason about complex series of chemical reactions.
Sometimes, during a series of chemical reactions, we may observe some substances which are unexpected side-products,
and we may not know, neither at which step of the process, nor how exactly, they were produced.
In such a setting, **_abductive reasoning_** helps us identify a set of possible explanations for what has actually happened. 

In this project, we use **_Prologica_** (https://www.researchgate.net/publication/228768630_ProLogICA_a_practical_system_for_Abductive_Logic_Programming),
a system for **Abductive Logic Programming (ALP)** with Negation as Failure (NAF) and Integrity Constraints (ICs).
Prologica is a meta-interpreter for **_Prolog_**, and its code is contained in a single Prolog file (**_alp.pl_**).
The project can be run, for example, with **_SWI-Prolog 7.4.0-rc2_**.
