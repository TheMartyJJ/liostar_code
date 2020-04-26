# LioStar

LioStar library enables IFC for FStar application

## Getting Started

These instruction explains how to build, run and generate profile of Lio, LioStar-static and LioStar-dynamic.

### Prerequisites

> Todo

### Clean

To clean the project type

```
make clean
```

### Build

#### Lio

1. Edit `Bus.Example.fst` and uncomment Lio include and make sure LioStar comment is uncommented.
2. run `make Bus.Example`

#### LioStar-static

1. Edit `Bus.Example.fst` and uncomment LioStar include and make sure Lio comment is uncommented.
2. Edit `Core.LioStar.fst` and set variable `isErased` to true, uncomment the correct helpers (more information in the file)
3. run `make Bus.Example`


#### LioStar-dynamic

1. Edit `Bus.Example.fst` and uncomment LioStar include and make sure Lio comment is uncommented.
2. Edit `Core.LioStar.fst` and set variable `isErased` to false, uncomment the correct helpers (more information in the file)
3. run `make Bus.Example`

### Run

For any version of `Bus.Example`, you can run it with

```
make run_Bus.Example
```

### Profiling

To profile a version of `Bus.Example`, you can type

```
make profile_Bus.Example
```

A file `Results.txt` containing all profiling information will be created.

> The file `Results.txt` is wiped at each profile.

### Count lines of code

To count line of code of any FStar file, invoke make with `NameOfFile`

```
make loc_NameOfFile
```
