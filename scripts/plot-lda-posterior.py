import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import os
import argparse
from scipy.special import rel_entr
import time
import math
import numpy as np
from scipy.special import gamma
parser = argparse.ArgumentParser(description=
        "Plot the marginalized log posterior of z ")

parser.add_argument('filepath', nargs='*', type=str,help= "Samples file")

# T: the number of topics
# W: the number of unique words, vocab size
# B: beta
# a: alpha
# D: the number of documents
def posterior(sample,docs,docids,T,W,B,a,D):
    n = np.zeros((T,W))
    ndt = np.zeros((D,T))
    for i, z in enumerate(sample):
        n[z,docs[i]] += 1
        ndt[docids[i],z] += 1
    lhs = pow(gamma(W*B)/ pow(gamma(B),W),T)
    rhs = 1
    for j in range(T):
        denom = gamma(sum(n[j]) + W*B)
        numer = 1
        for w in range(W):
            numer *= gamma(n[j,w]+B)
        rhs *= (numer/denom)
    p_w_z = lhs*rhs
    lhs = pow(gamma(T*a)/ pow(gamma(a),T),D)
    rhs = 1
    for d in range(D):
        denom = gamma(sum(ndt[d])+T*a)
        numer = 1
        for j in range(T):
            numer *= gamma(ndt[d,j]+a)
        rhs *= (numer/denom)
    p_z = lhs*rhs
    return math.log(p_z*p_w_z)

args = parser.parse_args()
docs = [2,0,1,2,2,2,0,2,2,2,2,2,2,0,2,1,2,2,2,1,2,2,1,2,1,0,1,2,1,1,0,2,0,0,2,3,0,3,2,2,2,2,0,1,0,2,0,1,2,2]
docids =[0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4]
z_true = [1,1,0,1,1,1,1,1,1,1,1,0,0,1,0,0,1,1,1,1,0,1,0,0,0,1,0,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,0,0,1]

z_webppl = [1,1,1,1,1,1,1,1,1,1,0,0,0,1,0,0,1,1,0,0,1,1,0,1,0,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,0,1,1,0,1,0,1,0,1,1]
z_webppl_20000 = [1,0,0,1,1,1,0,1,0,1,0,1,1,0,1,0,1,1,0,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,0,0,0,1,1,1,1,1,1,1,1,1,0,1,1]
z_webppl_100000 = [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1,0,0,1,0,0,1,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0]
z_webppl_1000000 = [1,1,1,1,0,1,1,0,1,0,0,0,0,1,0,1,1,0,0,1,1,0,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,0,0,0,1,0,0,1,0,0,0,1,0,0]
z = [z_webppl,z_webppl_20000,z_webppl_100000,z_webppl_1000000]
T = 2
W = 4
D = 5
a = 1.0
B = 1.0
samples = pd.read_csv(args.filepath[0],header=None,dtype=np.float64, sep=" ")
samples_sx = (samples.drop(columns=[0,len(samples.columns)-1],axis=1)).astype(float64)

post = []
for sample in samples_sx.values:#[-100000:]:
    post.append(posterior(sample, docs, docids, T, W, B, a, D))
print("True posterior: ", str(posterior(z_true,docs,docids,T,W,B,a,D)))
print("Last sample posterior: ",str(posterior(samples_sx.values[-1],docs,docids,T,W,B,a,D)))

print("Webppl posterior: ", str(posterior(z_webppl_1000000,docs,docids,T,W,B,a,D)))

plt.plot(post)
plt.show()
