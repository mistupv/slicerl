# ROOT_DIR = $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
# ERLC_DIR = $(shell which erlc)
# ERLC_PATH = $(shell dirname $(lastword $(ERLC_DIR)))


compile:
	@rm -Rf ebin
	@mkdir ebin
	@erlc -o ebin src/*.erl 
	@./check_dialyzer

clean:
	@rm -Rf ebin
	@find . -name '*.dump' -prune -exec rm -fr {} \;

# install:
# 	@make script_install FILE=pn_tools
# 	@make script_install FILE=pn_slicer
# 	@make script_install FILE=pn_prop

# script_install:
# 	@erl -pa ebin -run make_script from_path $(ROOT_DIR) $(FILE) -noshell -s erlang halt
# 	@chmod +x "$(FILE)_temp"
# 	@mv -f "$(FILE)_temp" $(ERLC_PATH)/$(FILE)
