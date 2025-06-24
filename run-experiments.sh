# To run the experiments, we call a Python script, for details see scripts/run-plot-transform-results-cppl.py
# The experiment outputs a data file under "data_results/" that gives the normalizing constants for each particle number for 30 runs
usage() {
    echo "Usage: bash run-experiments.sh jc toy"
    echo "Datasets:"
    echo "toy"
    echo "primates"
    echo "M336"
    echo "Models:"
    echo "jc"
    echo "gtr"
    echo "help"
}

model="$1"
dataset="$2"
case "$dataset" in
    "toy")
        echo "Running toy data"
        case "$model" in
            "jc")
                echo "Model: jc"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/jc/ --modelN jc --datasetName toy --filename tree-inference  --lstP 100 1000 10000 --numruns 30
                ;;
            "gtr")
                echo "Model: gtr"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/gtr/ --modelN gtr --datasetName toy --filename tree-inference-gtr --lstP 100 1000 10000 --numruns 30
                ;;
            *)
                echo "Invalid model specified"
                usage
                exit 1
                ;;
        esac
        ;;
    "primates")
        echo "Running primates data"
        case "$model" in
            "jc")
                echo "Model: jc"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/jc/ --modelN jc --datasetName primates --filename tree-inference  --lstP 100 1000 10000 --numruns 30
                ;;
            "gtr")
                echo "Model: gtr"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/gtr/ --modelN gtr --datasetName primates --filename tree-inference-gtr --lstP 100 1000 10000 --numruns 30
                ;;
            *)
                echo "Invalid model specified"
                usage
                exit 1
                ;;
        esac
        ;;
    "M336")
        echo "Running M336 data"
        case "$model" in
            "jc")
                echo "Model: jc"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/jc/ --modelN jc --datasetName M336 --filename tree-inference --lstP 100 1000 10000 --numruns 30
                ;;
            "gtr")
                echo "Model: gtr"
                python3 scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/gtr/ --modelN gtr --datasetName M336 --filename tree-inference-gtr --lstP 100 1000 10000 --numruns 30
                ;;
            *)
                echo "Invalid model specified"
                usage
                exit 1
                ;;
        esac
        ;;
    *)
        echo "Invalid dataset specified"
        usage
        exit 1
        ;;
esac


