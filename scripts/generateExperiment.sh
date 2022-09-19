dlist=(5 10 15 20 25 30 35 40 45 50)
for i in ${dlist[@]}; do
  python genLDAgenerator.py -outpath $5/lda$i-$1-$2.mc -vocabsize $1 -numdocs $i -numWordsPerDoc $2 -alpha 1.0 -beta 1.0 -k $3 -r $4
  cppl -m mexpr-importance $5/lda$i-$1-$2.mc
  ./out > $5/lda$i-$1-$2.mc
  sed -i '' -e '$ d' $5/lda$i-$1-$2.mc 
done
