# python genLDAgenerator.py -outpath ex.mc -vocabsize 3 -numdocs 3 -numWordsPerDoc 100 -alpha 1.0 -beta 1.0 -k 2
import csv
import pandas as pd
import sys
from sys import argv
from functools import reduce
import numpy as np
from pathlib import Path
import random
def getopts(argv):
    opts = {}
    while argv:
        if argv[0] == '-outpath':
            opts[argv[0][1:]] = argv[1]
        elif argv[0] == '-vocabsize':
            opts[argv[0][1:]] = int(argv[1])
        elif argv[0] == '-numdocs':
            opts[argv[0][1:]] = int(argv[1])
        elif argv[0] == '-numWordsPerDoc':
            opts[argv[0][1:]] = int(argv[1])
        elif argv[0] == '-alpha':
            opts[argv[0][1:]] = float(argv[1])
        elif argv[0] == '-beta':
            opts[argv[0][1:]] = float(argv[1])
        elif argv[0] == '-k':
            opts[argv[0][1:]] = int(argv[1])
        argv = argv[1:]
    return opts
    
if __name__ == '__main__':
    myargs = getopts(argv)
    outpath =  myargs['outpath']
    vocabsize = myargs['vocabsize']
    numdocs = myargs['numdocs']
    numWordsPerDoc = myargs['numWordsPerDoc']
    k = myargs['k']
    alpha = myargs['alpha']
    beta = myargs['beta']
    with open(outpath, 'w') as file:
        file.write("include \"string.mc\"\n")
        file.write("mexpr\n")
        file.write("let vocabsize:Int = " + str(vocabsize) + " in\n")
        file.write("let numdocs:Int = " + str(numdocs) + " in\n")
        file.write("let numWordsPerDoc:Int = " + str(numWordsPerDoc) + " in\n")
        file.write("let numtopics:Int = " + str(k) + " in\n")
        file.write("let a:Float = " + str(alpha)+ " in\n")
        file.write("let b:Float = "+ str(beta)+ " in\n")
        alphastr = "let alpha:[Float] = ["
        for i in range(k-1):
            alphastr += str(alpha) + ","
        alphastr += str(alpha) + "] in \n"
        file.write(alphastr)
        betastr = "let beta:[Float] = ["
        for i in range(k-1):
            betastr += str(beta) + ","
        betastr += str(beta) + "] in\n"
        file.write(betastr)
        file.write("let phi = map (lam. assume (Dirichlet beta)) (range 0 numtopics 1) in\n")
        file.write("let theta = map (lam. assume (Dirichlet alpha)) (range 0 numdocs 1) in\n")
        file.write("let docWords = map (lam docid.\nlet words = map (lam.\nlet z = assume (Categorical (get theta docid)) in\nlet w = assume (Categorical (get phi z)) in\n(z,w)) (range 0 numWordsPerDoc 1)\nin words) (range 0 numdocs 1) in\n")
        
        model = "let mcprogram = join [\"include \\\"string.mc\\\"\\ninclude \\\"seq.mc\\\"\nmexpr\\n\",\"let vocabsize:Int = \" ,int2string vocabsize, \" in\\n\",\n\
                      \"let numdocs:Int = \" ,int2string numdocs,\" in\\n\",\n\
                      \"let numtopics:Int = \", int2string numtopics, \" in\\n\",\n\
                      \"let alpha:[Float] = [\",\
                      foldl (lam acc. lam . concat (concat acc (float2string a)) \",\") \"\" (range 1 numtopics 1),float2string 1., \"] in\\n\",\n\
                      \"let beta:[Float] = [\",\
                      foldl (lam acc. lam . concat (concat acc (float2string b)) \",\") \"\" (range 1 vocabsize 1),\
                      float2string 1., \"] in\n\",\n\
                      \"let phi = map (lam. assume (Dirichlet beta)) (range 0 numtopics 1) in\\n\",\n\
                      \"let theta = map (lam. assume (Dirichlet alpha)) (range 0 numdocs 1) in\\n\",\n\
                      \"let docs:[Int] = [\",\n\
                      foldl (lam acc. lam doc. (foldl (lam s. lam w. join [s, int2string w.1, \",\"] ) acc doc )) \"\" (init docWords),\n\
                      foldl (lam s. lam w. join [s, int2string w.1, \",\"]) \"\" (init (last docWords)),\n\
                      join [int2string ((last (last docWords)).1), \"] in\\n\"],\n\
                      \"let docids:[Int] = [\",\n\
                       foldl (lam acc. lam doc. (foldl (lam s. lam. join [s, int2string doc, \",\"] ) acc (range 0 numWordsPerDoc 1) )) \"\" (range 0 (subi numdocs 1) 1),\n\
                       (foldl (lam s. lam . join [s, int2string (subi numdocs 1), \",\"] ) \"\" (range 1 numWordsPerDoc 1) ),\n\
                       join [int2string (subi numdocs 1), \"] in \\n\"],\n\
                       \"let topicassignments:[Int] = [\",\n\
                      foldl (lam acc. lam doc. (foldl (lam s. lam w. join [s, int2string w.0, \",\"] ) acc doc )) \"\" (init docWords),\n\
                      foldl (lam s. lam w. join [s, int2string w.0, \",\"]) \"\" (init (last docWords)),\n\
                      join [int2string ((last (last docWords)).0), \"] in\\n\"],\n\
                       \"let z = map (lam w.\\n\",\n\
                       \"let z = assume (Categorical (get theta (get docids w))) in\\n\",\n\
                       \"observe (get docs w) (Categorical (get phi z));\\n z) \",\n\
                       \"(range 0 (length docs) 1) in \\n\",\n"
        returnStr = "\"let str = foldl (lam acc. lam e. join [acc,float2string e,\\\" \\\"]) \\\"\\\" (get theta 0) in\\n\
                        let str = foldl (lam acc. lam e. join [acc,float2string e,\\\" \\\"]) str (get theta 1) in\\n\
                        let str = foldl (lam acc. lam e. join [acc,float2string e,\\\" \\\"]) str (get theta 2) in\\n\
                        let str = foldl (lam acc. lam e. join [acc,float2string e,\\\" \\\"]) str (get phi 0) in\\n\
                        foldl (lam acc. lam e. join [acc,float2string e,\\\" \\\"]) str (get phi 1) \\n\""
        model = model + returnStr + "] in mcprogram\n"
        file.write(model)
        file.close()
