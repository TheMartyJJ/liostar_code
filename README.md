# Organization of the source code

This tarball contains four directories. Due to lack of time, we have numerous LIOStar libraries.

- `Bus_And_MMU` contains {D,G,S}Lio libraries and a working and extractable implementation of the Bus* and MMU* examples.
- `DBStar` contains newer versions of {D,G,S}Lio libraries, and a working and extractable implementation of our DB* example.
- `Lib - Work In Progress` contains the latest libraries, however, things are not really stable for now. For taking a look at how {D,G,S}LIO libraries are implemented, this folder is the better.
- `NI_Lemmas` contains most of the functions that defines the non interference meta program.

## Bus_And_MMU

Experimentation requires updating the code according to the version of LIO\* :

1. DLIO\*: open the example file `Bus.Example.fst` or `MMU.Example.fst` and comment the line `open Core.LioStar` then uncomment the line `open Core.Lio`.
2. SLIO\*: open the example file `Bus.Example.fst` or `MMU.Example.fst` and comment the line `open Core.Lio` then uncomment the line `open Core.LioStar`. Then initialize the constant `target` to `C_Concrete`. Finally comment *erased mapXX* and uncomment the *non-erased mapXX*.
3. GLIO\* : open the example file `Bus.Example.fst` or `MMU.Example.fst` and comment the line `open Core.Lio` then uncomment the line `open Core.LioStar`. Then initialize the constant `target` to `C_Erased`. Finally comment *non-erased mapXX* and uncomment the *erased mapXX*.

Type `make Bus.Example.fst` or make MMU.Example.fst`. Then `time out/Bus.Example` or `time out/MMU.Example.fst`.

> You must be in the `Bus_And_MMU` directory.

## DBStar

The experiment takes place in the folder containing the desired example:

1. DLIO\*: `DBStar_LioStar_Lio`
2. SLIO\*: `DBStar_LioStar_Dynamic`
3. GLIO\*: `DBStar_LioStar_Static`

> Note: this version uses symbolic links.

Type `make DBStar run_DBStar`.
