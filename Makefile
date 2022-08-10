uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')

TOOL_DLL = TypeInjections/TypeInjections/bin/Debug/net6.0/TypeInjections.dll
TOOL_SLN = TypeInjections/TypeInjections.sln
TOOL_TEST = TypeInjections/TypeInjections.Test/TypeInjections.Test.fsproj
DAFNY_DIR = dafny
DAFNY = $(DAFNY_DIR)/dafny

ifeq ($(uname_S),Linux)
	DAFNY_DOWNLOAD_LOCATION = https://github.com/dafny-lang/dafny/releases/download/v3.3.0/dafny-3.3.0-x64-ubuntu-16.04.zip
	Z3_DOWNLOAD_LOCATION = https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip
	Z3 = z3-4.8.5-x64-ubuntu-16.04
endif

ifeq ($(uname_S),Darwin)
	DAFNY_DOWNLOAD_LOCATION = https://github.com/dafny-lang/dafny/releases/download/v3.3.0/dafny-3.3.0-x64-osx-10.14.2.zip
	Z3_DOWNLOAD_LOCATION = https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-osx-10.14.2.zip
	Z3 = z3-4.8.5-x64-osx-10.14.2
endif

DAFNY_ZIP = $(shell basename $(DAFNY_DOWNLOAD_LOCATION))
Z3_ZIP = $(shell basename $(Z3_DOWNLOAD_LOCATION))

.PHONY: $(DAFNY) all build deps install_dafny clean check_format format
.SILENT: $(DAFNY)

all: deps build

$(TOOL_DLL): $(DAFNY)
	dotnet build $(TOOL_SLN) -p:Configuration=Debug

build: deps $(TOOL_DLL)

$(DAFNY):
	if [ ! -d $(DAFNY_DIR) ]; then \
		echo "Installing Dafny" \
		&& curl $(DAFNY_DOWNLOAD_LOCATION) -L -o $(DAFNY_ZIP) \
		&& unzip $(DAFNY_ZIP) && rm $(DAFNY_ZIP);\
	else\
		echo "Dafny is already installed at $(DAFNY)";\
	fi

install_dafny: $(DAFNY)

deps: install_dafny

format:
	(cd TypeInjections && dotnet tool run fantomas -r .)

check_format:
	(cd TypeInjections && dotnet tool run fantomas --check -r .)

test: unit-test

unit-test: build
	dotnet test $(TOOL_TEST)

clean:
	rm -rf $(DAFNY_DIR)
	rm -rf TypeInjections/TypeInjections/bin/Debug
	rm -rf TypeInjections/TypeInjections.Tests/bin/Debug
