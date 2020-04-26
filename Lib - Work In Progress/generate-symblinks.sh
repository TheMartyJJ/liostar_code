cd Libraries
for system in DLio SLio GLio; do
    echo "./Libraries/$system"
    cd $system/
    find . -type l -ls -delete
    ln -s ../*.fst .
    cd ..
done
cd ..

cd Clients
for client in */; do
    cd $client
    for system in DLio SLio GLio; do
	echo "./Clients/$client/$system"
	mkdir -p $system
	cd $system
	find . -type l -ls -delete
	cp -n ../../../Libraries/$system/LioStar.Effect.Parameters.fst .
	find .. -type f -maxdepth 1 -name '*.fst' | xargs -IX ln -s "X" .
	ln -s ../../../Libraries/$system/*.fst .
	ln ../../Makefile.template Makefile
	cd ..
    done
    cd ..
done
cd ..
