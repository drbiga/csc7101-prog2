balance(matheus, 50).

can_afford(PERSON, ITEM_PRICE) :- balance(PERSON, PERSON_BALANCE), PERSON_BALANCE > ITEM_PRICE.
