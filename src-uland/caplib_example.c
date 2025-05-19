#include "caplib.h"
#include "user.h"

int main(void) {
  exo_cap page = cap_alloc_page();
  // use the page here ...
  cap_unbind_page(page);
  exit();
}
