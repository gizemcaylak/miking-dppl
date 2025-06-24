# Contributions of the paper
We implement our pruning algorithm in Miking DPPL [1]. We include the full source code for Miking DPPL, with our transformations added in miking-dppl/coreppl/src/coreppl-to-mexpr/pruning, and the models and datasets used originated from [3,4] under 'miking-dppl/coreppl/models/tree-inference'.
### There are two main files for pruning:
- The runtime file for the pruning algorithm: coreppl/src/coreppl-to-mexpr/pruning/runtime.mc
- The compile time file that takes the model and maps it to the runtime functions: coreppl/src/coreppl-to-mexpr/pruning/compile.mc

# How to run the experiments?
- To run the experiments first miking and miking-dppl should be installed. 
	- To install miking, you can refer to its GitHub repo: https://github.com/miking-lang/miking. We are specifically using the version at this commit https://github.com/miking-lang/miking/commit/cf546fb759c4a7c26552396b7587fec4cd5d1bc9
	- To install miking-dppl, we provide the source code. The README instructions specify how to install the miking-dppl. Prune is a flag in miking-dppl. 
- After installing miking and miking-dppl, go to miking-dppl folder. The experiments can be run with run-experiments script by choosing the dataset and the model. Type bash run-experiments.sh on your command line to see the options.
	- `bash run-experiments.sh <model> <dataset>` 
	<model>: jc, gtr
	<dataset>: toy, primates, M336
	- For example, to run toy dataset with jc model:`bash run-experiments.sh jc toy`
	- You can also change the number of particles to used for each experiment by changing the values of the arguments `--lstP` in `run-experiments.sh`. 
		- `--lstP` takes a sequence of particle counts (x-axis on the experiments) to run the model 
	- In default, we run each experiment 30 times; however, you can change the number of runs by changing the values of the arguments `--numruns`.
	- Or to prune a specific model, we can use the `cppl` command via
		`cppl path/to/model --prune`, e.g. `cppl coreppl/models/tree-inference/jc/automated-pruning/tree-inference-auto-toy.mc --prune`
	- You can check the miking-dppl/README.md or type `cppl` to see the detailed information on the command arguments.

# How to run further tests?
- You can run the tests related to pruning via `make -s -f test-coreppl.mk pruning`
# Dependency list
Before running the experiments, make sure that you have the neccessary dependencies indicated below for the Python script.
- `os`
- `argparse`
- `seaborn`
- `pandas`
- `matplotlib`
- `subprocess`
- `time`
- `numpy`

These can be installed via
`pip install os argparse seaborn pandas scipy matplotlib numpy subprocess time`

For more details on the called python script please refer to the `miking-dppl/scripts/run-plot-transform-results-cppl.py`

# References
## For the tools
[1] Lunden, D.;Ohman, J.; Kudlicka, J.; Senderov, V.; Ronquist, F.; and Broman, D. 2022. Compiling Universal Probabilistic
Programming Languages with Efficient Parallel Sequential Monte Carlo Inference. In Sergey, I., ed., Programming Languages and Systems, 29–56. Cham: Springer International Publishing. ISBN 978-3-030-99336-8.
[2] Broman, D. 2019. A Vision of Miking: Interactive Programmatic Modeling, Sound Language Composition, and Self-Learning Compilation. In Proceedings of the 12th ACM SIGPLAN International Conference on Software Language Engineering, 55–60. Association for Computing Machinery

## For the datasets
[3] Clemens Lakner, Paul van der Mark, John P. Huelsenbeck, Bret Larget, and Fredrik Ronquist. 2008. Efficiency of
Markov Chain Monte Carlo Tree Proposals in Bayesian Phylogenetics. Systematic Biology 57, 1 (02 2008), 86–103.
https://doi.org/10.1080/10635150801886156 arXiv:https://academic.oup.com/sysbio/article-pdf/57/1/86/24205420/57-
1-86.pdf
[4] Liangliang Wang, Shijia Wang, and Alexandre Bouchard-Côté. 2019. An Annealed Sequential Monte Carlo Method
for Bayesian Phylogenetics. Systematic Biology 69, 1 (06 2019), 155–183. https://doi.org/10.1093/sysbio/syz028
arXiv:https://academic.oup.com/sysbio/article-pdf/69/1/155/31455804/syz028.pdf


