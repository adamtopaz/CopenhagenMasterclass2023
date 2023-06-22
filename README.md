# Formalizing Condensed Mathematics

This is the central repository for the [2023 masterclass](https://www.math.ku.dk/english/calendar/events/formalisation-of-mathematics/) on the formalization of condensed mathematics, taking place in 2023 at Copehnagen.

## Installation

### Local installation

This is the best way; you can edit files and experiment, and you won't lose them.
It's also the hardest way: it involves typing stuff in on the command line. 

In brief: first install Lean 4 following the installation instructions from the community webpage [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then download and install this project by typing

```
git clone git@github.com:adamtopaz/CopenhagenMasterclass2023
cd CopenhagenMasterclass2023
lake exe cache get
lake build
```

Finally, open the root directory of the project folder in VS Code (for example by typing `code .`, or by opening VS Code and then clicking `File -> Open Folder` and opening the `CopenhagenMasterclass2023` folder). Say that you trust the authors of the code -- 
and you can now open the Lean files in the repository and Lean should run on them automatically.

Additional instructions for working on an existing Lean4 project can be found [here](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project). 

### Codespaces

This repository is configured for use with github's codespaces.
To get started with codespaces in this repo, just click the green "code" icon to create a new codespace.
More detailed instructions can be found [here](https://docs.github.com/en/codespaces/developing-in-codespaces/creating-a-codespace-for-a-repository).

## Schedule

Each day is split in two, with lectures by KB and AT in the morning, and time for group work and discussions in the afternoon.
The general plan for each day is listed below. 

### Monday

- Overview and logistics.
- Category theory in Lean4.
- Condensed objects in Lean4.

### Tuesday and Wednesday

- Sheaves on `CompHaus`, `Profinite` and `ExtrDisc`.
- Equivalences between the three categories of sheaves.

### Thursday and Friday

- Abelian Categories, Grothendieck's AB axioms.
- AB axioms for condensed abelian groups.