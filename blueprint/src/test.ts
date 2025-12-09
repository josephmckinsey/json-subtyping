type Person =
    | { age: number, id: number }
    | { dob: Date }

function getPerson(): Person {
    const obj = { dob: new Date('2000-01-01'), age: 12 };
    return obj;  // Does this compile? Let's see!
}

const person = getPerson();
console.log("Person:", person);

if ("age" in person) {
    console.log("Has age property");

    // Can we access age directly?
    console.log("person.age =", person.age);

    // Can we access id directly?
    console.log("person.id =", person.id);
}
