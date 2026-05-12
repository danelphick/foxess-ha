import { describe, it, expect, vi, beforeAll, afterEach } from 'vitest';

beforeAll(async () => {
  await import('../custom_components/foxess/scheduler_card.js');
});

afterEach(() => {
  document.body.innerHTML = '';
});

const DEVICE_SN = 'SN123456';

const TEMPLATE_GROUPS = [
  { startMins: 0, endMins: 360, enable: 1, workMode: 'ForceCharge',
    minSocOnGrid: 10, fdSoc: 90, fdPwr: 0, maxSoc: 100 },
];

function makeHass({ schedulerState = 'enabled', send = null, templates = [] } = {}) {
  const defaultSend = vi.fn().mockImplementation(msg => {
    if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates });
    return Promise.resolve({ ok: true });
  });
  return {
    states: {
      'sensor.foxess_scheduler_enabled': {
        state: schedulerState,
        attributes: { friendly_name: 'FoxESS Scheduler Enabled' },
      },
      'sensor.foxess_scheduler_groups': {
        state: '0',
        attributes: { groups: [], device_sn: DEVICE_SN },
      },
    },
    connection: {
      sendMessagePromise: send ?? defaultSend,
    },
  };
}

function mountCard(hass) {
  const Card = customElements.get('foxess-scheduler-card');
  const card = new Card();
  document.body.appendChild(card);
  card.hass = hass;
  return card;
}

async function tick() {
  await new Promise(resolve => setTimeout(resolve, 0));
}

// ---------------------------------------------------------------------------
// Use template dropdown
// ---------------------------------------------------------------------------

describe('Use template dropdown', () => {
  it('shows "No templates" text when no templates exist', async () => {
    const card = mountCard(makeHass({ templates: [] }));
    await tick();
    expect(card.shadowRoot.querySelector('.tpl-select')).toBeNull();
    expect(card.shadowRoot.querySelector('.tpl-none')?.textContent).toBe('No templates');
  });

  it('shows template names after get_templates resolves', async () => {
    const card = mountCard(makeHass({ templates: [{ name: 'Morning', groups: TEMPLATE_GROUPS }] }));
    await tick();
    const sel = card.shadowRoot.querySelector('.tpl-select');
    expect(sel).not.toBeNull();
    const options = Array.from(sel.options).map(o => o.text);
    expect(options).toContain('Morning');
  });

  it('sends foxess/get_templates on mount with the device SN', async () => {
    const send = vi.fn().mockResolvedValue({ templates: [] });
    mountCard(makeHass({ send }));
    await tick();
    expect(send).toHaveBeenCalledWith(
      expect.objectContaining({ type: 'foxess/get_templates', deviceSN: DEVICE_SN })
    );
  });

  it('opens edit modal with template groups when a template is selected', async () => {
    const card = mountCard(makeHass({ templates: [{ name: 'Morning', groups: TEMPLATE_GROUPS }] }));
    await tick();
    const sel = card.shadowRoot.querySelector('.tpl-select');
    sel.value = '0';
    sel.dispatchEvent(new Event('change'));
    const dialog = card.shadowRoot.querySelector('dialog');
    expect(dialog).not.toBeNull();
    expect(dialog.open).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Save as template in edit modal
// ---------------------------------------------------------------------------

describe('Save as template in edit modal', () => {
  function openEditModal(card) {
    card.shadowRoot.querySelector('.edit-btn').click();
  }

  it('tpl-open-btn is present in the edit modal footer', () => {
    const card = mountCard(makeHass());
    openEditModal(card);
    expect(card.shadowRoot.querySelector('.tpl-open-btn')).not.toBeNull();
  });

  it('tpl-form is hidden initially', () => {
    const card = mountCard(makeHass());
    openEditModal(card);
    const form = card.shadowRoot.querySelector('.tpl-form');
    expect(form.style.display).toBe('none');
  });

  it('tpl-open-btn click reveals the template form', () => {
    const card = mountCard(makeHass());
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();
    const form = card.shadowRoot.querySelector('.tpl-form');
    expect(form.style.display).not.toBe('none');
  });

  it('second tpl-open-btn click hides the form again', () => {
    const card = mountCard(makeHass());
    openEditModal(card);
    const btn = card.shadowRoot.querySelector('.tpl-open-btn');
    btn.click();
    btn.click();
    const form = card.shadowRoot.querySelector('.tpl-form');
    expect(form.style.display).toBe('none');
  });

  it('tpl-cancel-btn hides the form', () => {
    const card = mountCard(makeHass());
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();
    card.shadowRoot.querySelector('.tpl-cancel-btn').click();
    expect(card.shadowRoot.querySelector('.tpl-form').style.display).toBe('none');
  });

  it('tpl-save-btn calls foxess/save_template with the entered name and current groups', async () => {
    const send = vi.fn().mockImplementation(msg => {
      if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
      return Promise.resolve({ ok: true });
    });
    const card = mountCard(makeHass({ send }));
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();

    const nameInput = card.shadowRoot.querySelector('.tpl-name-input');
    nameInput.value = 'Night charge';
    card.shadowRoot.querySelector('.tpl-save-btn').click();
    await tick();

    expect(send).toHaveBeenCalledWith(
      expect.objectContaining({
        type: 'foxess/save_template',
        deviceSN: DEVICE_SN,
        name: 'Night charge',
      })
    );
  });

  it('tpl-form is hidden after a successful save', async () => {
    const send = vi.fn().mockImplementation(msg => {
      if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
      return Promise.resolve({ ok: true });
    });
    const card = mountCard(makeHass({ send }));
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();
    card.shadowRoot.querySelector('.tpl-name-input').value = 'My template';
    card.shadowRoot.querySelector('.tpl-save-btn').click();
    await tick();
    expect(card.shadowRoot.querySelector('.tpl-form').style.display).toBe('none');
  });

  it('shows error text when foxess/save_template call fails', async () => {
    const send = vi.fn().mockImplementation(msg => {
      if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates: [] });
      if (msg.type === 'foxess/save_template') return Promise.reject(new Error('Server error'));
      return Promise.resolve({ ok: true });
    });
    const card = mountCard(makeHass({ send }));
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();
    card.shadowRoot.querySelector('.tpl-name-input').value = 'Bad save';
    card.shadowRoot.querySelector('.tpl-save-btn').click();
    await tick();
    const errEl = card.shadowRoot.querySelector('.tpl-error');
    expect(errEl.textContent).toBe('Server error');
  });

  it('selecting an existing template pre-fills the name input', async () => {
    const templates = [{ name: 'Morning', groups: TEMPLATE_GROUPS }];
    const send = vi.fn().mockImplementation(msg => {
      if (msg.type === 'foxess/get_templates') return Promise.resolve({ templates });
      return Promise.resolve({ ok: true });
    });
    const card = mountCard(makeHass({ send, templates }));
    await tick();
    openEditModal(card);
    card.shadowRoot.querySelector('.tpl-open-btn').click();

    const exSel = card.shadowRoot.querySelector('.tpl-existing-sel');
    exSel.value = '0';
    exSel.dispatchEvent(new Event('change'));

    expect(card.shadowRoot.querySelector('.tpl-name-input').value).toBe('Morning');
  });
});
