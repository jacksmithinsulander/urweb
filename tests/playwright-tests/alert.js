/** Click link, expect alert "You clicked it!  That's some fancy shooting!" */
module.exports = async (page, baseUrl) => {
  await page.goto(baseUrl + '/Alert/main');
  let dialogMsg = null;
  page.once('dialog', async dialog => {
    dialogMsg = dialog.message();
    await dialog.accept();
  });
  await page.click('xpath=/html/body/a');
  if (dialogMsg !== "You clicked it!  That's some fancy shooting!") {
    throw new Error(`Expected alert "You clicked it!  That's some fancy shooting!", got: ${dialogMsg}`);
  }
};
