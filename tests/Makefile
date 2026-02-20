all: test.o

test.o: test.c
	gcc -c test.c -o test.o

# Run all portable shell tests (no browser required)
test::
	./driver.sh aborter
	./driver.sh aborter2
	./driver.sh agg
	./driver.sh align
	./driver.sh ascdesc
	./driver.sh attrs_escape
	./driver.sh bindpat
	./driver.sh bool
	./driver.sh both
	./driver.sh both2
	./driver.sh case
	./driver.sh caseMod
	./driver.sh cdataF
	./driver.sh cdataL
	./cffi.sh
	./driver.sh entities
	./driver.sh fact
	./driver.sh filter
	./driver.sh jsonTest
	./driver.sh utf8
	./endpoints.sh

# Tests that require a real browser (Selenium + Chrome)
# See browser/ subdirectory
browser-test::
	@echo "Browser tests require: pip install selenium, chromedriver"
	@echo "Run individually, e.g.: ./driver-browser.sh active"
