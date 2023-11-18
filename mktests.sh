#/bin/sh

for i in `find . tests/ | grep mhs$`; do
    DIR=`dirname ${i}`
    FILE=`basename -s .mhs ${i}`
    stack exec tyinf -- --dump parser --no-colour ${i} > ${DIR}/${FILE}.out
done
