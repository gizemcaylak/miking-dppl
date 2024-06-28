# Contributions of the paper
We implement delayed sampling algorithms in Miking DPPL [1]. We include the full source code for Miking DPPL, with 
- the static transformations added in miking-dppl/coreppl/src/static-delay.mc
- with dynamically delayed sampling in miking-dppl/coreppl/src/coreppl-to-mexpr/delayed-sampling
- and the models and datasets[3,4,5] under 'miking-dppl/coreppl/models/experiments'.
### There are two main files for dynamic delayed:
- The runtime file for the delayed algorithm: coreppl/src/coreppl-to-mexpr/delayed-sampling/runtime.mc
- The compile time file that takes the model and maps it to the runtime functions: coreppl/src/coreppl-to-mexpr/delayed-sampling/compile.mc

# How to run the experiments?
- To run the experiments first miking and miking-dppl should be installed. 
	- To install miking, you can refer to its GitHub repo: https://github.com/miking-lang/miking. We are specifically using the version at this commit X
	- To install miking-dppl, we provide the source code. The README instructions under miking-dppl folder specify how to install the miking-dppl. --static-delay, and --dynamic-delay are flags in miking-dppl (see below, they need to be used with other flags). 
- After installing miking and miking-dppl, go to miking-dppl folder. The experiments can be run with run-experiments script by choosing the dataset and the model. Type bash run-experiments.sh on your command line to see the options.
	- `bash run-experiments.sh <model> <dataset> <numruns>`, e.g. bash run-experiments.sh lda lw 10
	<model>: lda, blr, vbd
	<dataset>: lw, c3, nips40, vbd-data, housing
	<numruns>: is an integer number to indicate the number of runs,e.g., 30
	- For example, to run lw dataset with lda model:`bash run-experiments.sh lda lw 10`
	- You can also change the number of particles to used for each experiment by changing the values of the arguments `--lstP` in `run-experiments.sh`. 
		- `--lstP` takes a sequence of particle counts (x-axis on the experiments) to run the model 
	- Or to delay a specific model statically, we can use the `cppl` command via
		`cppl path/to/model --extract-simplification inline --cps none --static-delay`, e.g. `cppl coreppl/models/experiments/lda/static-delayed/lda-lw.mc --extract-simplification inline --cps none --static-delay`
	- Or to delay a specific model dynamically, we can use the `cppl` command via
		`cppl path/to/model --extract-simplification inline --cps none --dynamic-delay`, e.g. `cppl coreppl/models/experiments/vbd/dynamic-delayed/vbd.mc --extract-simplification inline --cps none --dynamic-delay`
	- You can check the miking-dppl/README.md or type `cppl` to see the detailed information on the command arguments.

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
[3] Wingate, D.; Stuhlmueller, A.; and Goodman, N. 2011. Lightweight Implementations of Probabilistic Programming Languages Via Transformational Compilation. In Proceedings of the 14th International Conference on Artificial Intelligence and Statistics, volume 15, 770–778. PMLR.

[4] Ritchie, D.; Stuhlmuller, A.; and Goodman, N. 2016. C3:Lightweight Incrementalized MCMC for Probabilistic Programs using Continuations and Callsite Caching. In Proceedings of the 19th International Conference on Artificial Intelligence and Statistics, volume 51, 28–37. Cadiz, Spain: PMLR.

[5] Lunden, D.; Caylak, G.; Ronquist, F.; and Broman, D. 2023. Automatic alignment in higher-order probabilistic programming languages. Programming Languages and Systems LNCS 13990, 535.

