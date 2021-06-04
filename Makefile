BEAM_FILES = $(patsubst src/%.erl,ebin/%.beam,$(wildcard src/**.erl))

compile: ebin/ $(BEAM_FILES)

ebin/%.beam: src/%.erl
	erlc -o ebin $<

ebin/:
	mkdir -p ebin

dialyzer:
	dialyzer --build_plt --apps erts kernel stdlib mnesia --output_plt .dialyzer_plt

clean:
	rm -rf ebin
	rm -rf .dialyzer_plt
