# For each of the cases run with automated and hard-coded pruning and without pruning with increasing number of particles
# Save a graph as pdf where x-axis is the number of particles and y-axis is the normalizing constant
# Save them in a dat format as well
# nohup python scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/jc/ --modelN jc --datasetName toy --datasetIdent jc --filename tree-inference --lstP 100 1000 10000 --numruns 30 &
# nohup python scripts/run-plot-transform-results-cppl.py coreppl/models/tree-inference/jc/ --modelN jc --datasetName primates --datasetIdent jc --filename tree-inference --lstP 100 1000 10000 --numruns 30 &

import os
import argparse
import seaborn as sns
import pandas as pd
import matplotlib.pyplot as plt
import subprocess
import time
import numpy as np
parser = argparse.ArgumentParser(description=
        "Compile and run the model with specified number of particles and plot the normalizing constants")
parser.add_argument('filepath', nargs='*', type=str,help= "File path of the model")
parser.add_argument('--numruns',  type=int, default=100)
parser.add_argument('--modelN',  type=str, default="jc")
parser.add_argument('--filename',  type=str, default="tree-inference")
parser.add_argument('--datasetName',  type=str, default="toy")
parser.add_argument('--datasetIdent',  type=str, default="")
parser.add_argument('--lstP', nargs='+', type=int, default=[100,1000,10000,100000,1000000],help='A list of particles')

args = parser.parse_args()
resdir = "data_results/" + args.datasetName + args.datasetIdent
datasetName = args.datasetName
isExist = os.path.exists(resdir)
if not isExist:
    os.makedirs(resdir)
outname = 'out.mc'
numparticles= args.lstP
modelN = args.modelN
filenameS = args.filename

def plot_box(data1,label1,data2,label2,data3,label3,xrange):
    sns.set(style="darkgrid")
    dfs =[]

    for ind,p in enumerate(xrange):
        df = pd.DataFrame(np.column_stack((data1[ind],data2[ind],data3[ind])),columns=[label1,label2,label3]).assign(N=p)
        dfs.append(df)
    cdf = pd.concat(dfs)
    mdf = pd.melt(cdf, id_vars=['N'], var_name=['Method']) 
    mdf.rename(columns={"value": "Log(z)"}, inplace=True) 
    ax = sns.boxplot(x="N", y="Log(z)", hue="Method", data=mdf)  # RUN PLOT   
    plt.savefig(resdir +'/box_plot' + modelN + '.pdf')

filepath = args.filepath[0]
filepathAuto = filepath + "automated-pruning/" + filenameS
numruns = args.numruns
norm_auto_pruned = []
subprocess.run(['cppl',  filepathAuto + "-" +"auto" + "-" + datasetName + ".mc", '-m', 'smc-bpf', '--no-print-samples','--prune','--cps','partial','--resample','manual'])
filenameT =  resdir + "/time" + modelN + "-" + datasetName +  "-" +"auto" + ".dat"
fT = open(filenameT, "w")
fT.write("particles\truntime\tstd\n")
for i,p in enumerate(numparticles):
    fT.write(f"{p}\t")
    elapsed_time = np.zeros(numruns)
    filename = resdir + "/logz" + modelN + "-" + datasetName + "-" +"auto-" + str(i+1) + ".dat"
    f = open(filename, "w")
    f.write("data\n")
    norm_constants = np.zeros(numruns)
    for r in range(numruns):
        # Record the starting time
        start_time = time.time()
        result = subprocess.run(['./out', str(p)], stdout=subprocess.PIPE)
        # Record the ending time
        end_time = time.time()
        # Calculate the elapsed time
        elapsed_time[r] = (end_time - start_time)
        result_transformation = result.stdout.decode('utf-8')
        norm_constants[r] = float(result.stdout.decode('utf-8'))
        f.write(str(norm_constants[r]) +"\n")
    
    norm_auto_pruned.append(norm_constants) 
    elapsed_time_mean = np.mean(elapsed_time)
    elapsed_time_std = np.std(elapsed_time)
    fT.write(f"{elapsed_time_mean}\t")
    fT.write(f"{elapsed_time_std}\n")
    f.close()
subprocess.run(['rm', './out'])
fT.close()


filepathNoprune = filepath + "no-pruning/" + filenameS
subprocess.run(['cppl',  filepathNoprune + "-" + datasetName + ".mc", '-m', 'smc-bpf', '--no-print-samples','--cps','partial','--resample','manual'])

norm_nonpruned = []
filenameT =  resdir + "/time" + modelN + "-" + datasetName + "-" + "noprune" + ".dat"
fT = open(filenameT, "w")
fT.write("particles\truntime\tstd\n")
for i,p in enumerate(numparticles):
    fT.write(f"{p}\t")
    elapsed_time = np.zeros(numruns)
    filename =  resdir + "/logz" + modelN + "-" + datasetName + "-" + "noprune" + "-" + str(i+1) + ".dat"
    f = open(filename, "w")
    f.write("data\n")
    norm_constants = np.zeros(numruns)
    for r in range(numruns):
        # Record the starting time
        start_time = time.time()
        result = subprocess.run(['./out', str(p)], stdout=subprocess.PIPE)
        # Record the ending time
        end_time = time.time()
        # Calculate the elapsed time
        elapsed_time[r] = (end_time - start_time)
        result_transformation = result.stdout.decode('utf-8')
        norm_constants[r] = float(result.stdout.decode('utf-8'))
        f.write(str(norm_constants[r]) +"\n")
    
    norm_nonpruned.append(norm_constants) 
    elapsed_time_mean = np.mean(elapsed_time)
    elapsed_time_std = np.std(elapsed_time)
    fT.write(f"{elapsed_time_mean}\t")
    fT.write(f"{elapsed_time_std}\n")
    f.close()
subprocess.run(['rm', './out'])
fT.close()


filepathHardcoded = filepath + "hardcoded-pruning/" + filenameS
subprocess.run(['cppl',  filepathHardcoded +"-pruned" + "-" + datasetName + ".mc", '-m', 'smc-bpf','--no-print-samples','--cps','partial','--resample','manual'])
norm_hardpruned = []
filenameT =  resdir + "/time" + modelN + "-" + datasetName + "-" + "hardcoded" + ".dat"
fT = open(filenameT, "w")
fT.write("particles\truntime\tstd\n")
for i,p in enumerate(numparticles):
    fT.write(f"{p}\t")
    elapsed_time = np.zeros(numruns)
    filename =  resdir + "/logz" + modelN + "-" + datasetName + "-" + "hardcoded" + "-" + str(i+1) + ".dat"
    f = open(filename, "w")
    f.write("data\n")
    norm_constants = np.zeros(numruns)
    for r in range(numruns):
        # Record the starting time
        start_time = time.time()
        result = subprocess.run(['./out', str(p)], stdout=subprocess.PIPE)
        # Record the ending time
        end_time = time.time()
        # Calculate the elapsed time
        elapsed_time[r] = (end_time - start_time)
        result_transformation = result.stdout.decode('utf-8')
        norm_constants[r] = float(result.stdout.decode('utf-8'))
        f.write(str(norm_constants[r]) +"\n")
    
    norm_hardpruned.append(norm_constants) 
    elapsed_time_mean = np.mean(elapsed_time)
    elapsed_time_std = np.std(elapsed_time)
    fT.write(f"{elapsed_time_mean}\t")
    fT.write(f"{elapsed_time_std}\n")
    f.close()
subprocess.run(['rm', './out'])
fT.close()

# plot_box(norm_nonpruned, "No pruning",norm_hardpruned,"Hardcoded pruning",norm_auto_pruned, "Pruning",numparticles)


