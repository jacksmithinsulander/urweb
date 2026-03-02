/** Cffi test 1: submit form 1 -> effect page, click "Local" -> alert "<<Hoho>>", click "Either" -> "Hi there!" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Cffi/main');
  // Submit form 1 to navigate to effect page
  await page.click('xpath=/html/body/form[1]/input');
  await page.waitForSelector('xpath=/html/body/button[2]');
  // Click "Local" button (button[2]) which calls bar("Hoho") -> alert("<<Hoho>>")
  let dialogMsg1 = null;
  page.once('dialog', async dialog => {
    dialogMsg1 = dialog.message();
    await dialog.accept();
  });
  await page.click('xpath=/html/body/button[2]');
  if (dialogMsg1 !== '<<Hoho>>') {
    throw new Error(`Expected "<<Hoho>>", got: ${dialogMsg1}`);
  }
  // Click "Either" button (button[3]) which calls print() -> alert("Hi there!")
  let dialogMsg2 = null;
  page.once('dialog', async dialog => {
    dialogMsg2 = dialog.message();
    await dialog.accept();
  });
  await page.click('xpath=/html/body/button[3]');
  if (dialogMsg2 !== 'Hi there!') {
    throw new Error(`Expected "Hi there!", got: ${dialogMsg2}`);
  }
};
