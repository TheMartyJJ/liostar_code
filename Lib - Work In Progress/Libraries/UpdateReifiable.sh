for system in DLio GLio; do
    echo "Patches ./$system..."
    cd $system
    echo "/// This module is a auto-generated copy of \`LioStar.Effect.fst\`" > LioStar.Effect.FullyReifiable.fst
    echo "/// Usage: make a symbolic link of this file to some other directory as \`LioStar.Effect.fst\`" >> LioStar.Effect.FullyReifiable.fst
    cat LioStar.Effect.fst | \
	sed "s/.*/&{:NEW_LINE:}/" | \
	awk '{print}' ORS='' | \
	perl -ne 'while (1) {last unless s/\(\* MACRO((?:(?!\*\)).)+)/(* macro expansion begins *)\1(* macro expansion ends /}; print' | \
	sed 's/{:NEW_LINE:}/\n/g' >> LioStar.Effect.FullyReifiable.fst
    cd ..
done
