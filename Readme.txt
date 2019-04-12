
Prerequisites:
    python3 (>= 3.5)
    OCaml (= 4.07.0)
              OCaml libraries: depext ocamlbuild utop yojson zarith num omd menhir linenoise async_unix
	PVS (= 7.0.639)
		http://www.csl.sri.com/users/owre/drop/pvs-snapshots/


Install lem/linksem/sail and setup the environment for Sail-to-PVS parser
1. Download lem:
$ git clone https://github.com/rems-project/lem

2. Set up the Sail to PVS parser environment
$ cd Sail2PVS
$ ./sail2pvs.py --setup
$ cd ..

3. Make and install Lem
$ cd lem
$ make
$ cd ocaml-lib
$ make install
$ cd ../..

4. Generate PVS files for the Lem basic library
$ cd Sail2PVS
$ ./sail2pvs.py --library
$ cd ..

5. Configure and install linksem/ott/sail
$ git clone https://github.com/rems-project/linksem.git
$ cd linksem
$ make && make install
$ cd ..
$ git clone https://github.com/ott-lang/ott.git
$ cd ott
$ make
$ export LEM_DIR=$PWD
$ cd ..
Configure the environment variable:
    export LEMLIB=/path/to/lem/library
    export PATH=/path/to/ott/bin:/path/to/lem:${PATH}
$ git clone https://github.com/rems-project/sail.git
$ cd sail
$ make
$ make isail
$ sudo apt install m4 libgmp-dev z3
$ export SAIL_DIR=$PWD
$ test/run_tests.sh
$ cd ..
Configure the environment variable:
    export SAIL_DIR=/path/to/sail
    export PVS_HOME=/path/to/pvs

The structure of all the required directories:
-- lem
-- linksem
-- ott
-- sail
-- Sail2PVS
-- OPEV

Automatically translate a Sail project to OCaml and PVS (For example, mips):
1. Download the Cheri/Mips specification
$ git clone https://github.com/CTSRD-CHERI/sail-cheri-mips.git
2. Add the detailed information regarding the Sail project to tag.json, for example:
    "mips": {
        "sail_src_path": "../sail-cheri-mips/mips",
        "sail_src_files": "trace.sail prelude.sail mips_prelude.sail mips_tlb_stub.sail mips_wrappers.sail mips_ast_decl.sail mips_insts.sail mips_ri.sail mips_epilogue.sail",
        "lem_src_files": "mips_no_tlb.lem mips_extras.lem",
        "lem_embedded_lib": "Mips_extras",
        "lem_object_name": "mips_no_tlb",
        "target_dir": "./pvs_mips"
    }
3. Under the Sail2PVS directory:
$ ./sail2pvs.py --parse mips