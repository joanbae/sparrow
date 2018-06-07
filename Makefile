.PHONY: all sparrow sparrow_vis install uninstall clean

ROOT_DIR:=$(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

all: sparrow sparrow_vis

sparrow:
	jbuilder build @install sparrow
	@ln -f -s $(ROOT_DIR)/_build/default/main.exe sparrow

sparrow_vis:
	jbuilder build @install sparrow_vis
	@ln -f -s $(ROOT_DIR)/_build/default/vis.exe sparrow_vis

install: sparrow sparrow_vis
	jbuilder install sparrow

uninstall: sparrow sparrow_vis
	jbuilder uninstall sparrow

clean:
	jbuilder clean
	@rm -f $(ROOT_DIR)/sparrow $(ROOT_DIR)/sparrow_vis
